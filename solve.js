// solve.js — a fast, dependency-free re-implementation of makefun-site 1.0.0's build.
//
// run(input) returns exactly the output tree makefun-site 1.0.0's build returns for the input:
// a JSON object of every path it writes and that file's text, byte for byte.
//
// It runs the same pipeline (sources, front matter, permalinks, Markdown, collections, tags,
// layouts, report), rewritten for speed: plain-text runs are escaped in bulk instead of one
// character at a time, slugs are memoised and take a fast path when their text is ASCII, line
// endings and front matter are found by index instead of split and re-join, a page reuses the
// card its post already built, and tag slugs are computed once per name instead of four times.
// Nothing is cached from one run to the next: every cache below is made inside build() and
// dropped with it.

const REPORT_FILE = 'build-report.txt';
const RESERVED = ['posts', 'tags', 'page'];

/** Code-unit order (never the locale's). */
const byCodeUnits = (a, b) => (a < b ? -1 : a > b ? 1 : 0);

const dirOf = (path) => (path.includes('/') ? path.slice(0, path.lastIndexOf('/')) : '');

// ---------------------------------------------------------------- text

const ESCAPES = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };

/** `text` with & < > " and ' escaped. */
function escapeHtml(text) {
  const re = /[&<>"']/g;
  let out = '';
  let last = 0;
  let m;
  while ((m = re.exec(text)) !== null) {
    out += text.slice(last, m.index) + ESCAPES[m[0]];
    last = m.index + 1;
  }
  if (last === 0) return text;
  out += text.slice(last);
  return out;
}

/** The most characters a slug keeps before a collision suffix. */
const SLUG_MAX = 64;

/** The slug of ASCII `plain`: A-Z lowered, every run of characters other than a-z and 0-9 one "-", none at either end, at most SLUG_MAX characters (a "-" left at the cut dropped), "untitled" when nothing is left. */
function slugAscii(plain) {
  let out = '';
  let gap = false;
  for (const ch of plain) {
    let keep = null;
    if (ch >= 'A' && ch <= 'Z') keep = ch.toLowerCase();
    else if ((ch >= 'a' && ch <= 'z') || (ch >= '0' && ch <= '9')) keep = ch;
    if (keep === null) {
      gap = out.length > 0;
      continue;
    }
    if (gap) out += '-';
    gap = false;
    out += keep;
  }
  out = out.slice(0, SLUG_MAX).replace(/-+$/, '');
  return out === '' ? 'untitled' : out;
}

/** The slug of `text`, memoised in `memo` (one build's worth). */
function slugify(text, memo) {
  const hit = memo.get(text);
  if (hit !== undefined) return hit;
  // NFKD is the identity on ASCII and no combining mark occurs there, so the character loop alone is exact.
  const out = /[^\x00-\x7F]/.test(text) ? slugAscii(text.normalize('NFKD').replace(/\p{M}/gu, '')) : slugAscii(text);
  memo.set(text, out);
  return out;
}

/** `slug` made unique against `taken` (and added to it): the first of slug, slug-2, slug-3 ... not taken. */
function uniqueSlug(slug, taken) {
  let out = slug;
  for (let n = 2; taken.has(out); n++) out = `${slug}-${n}`;
  taken.add(out);
  return out;
}

const MONTHS = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];

/** A YYYY-MM-DD date in words, from the string alone: "2026-11-09" is "9 November 2026". */
function longDate(date) {
  const [y, m, d] = date.split('-');
  return `${Number(d)} ${MONTHS[Number(m) - 1]} ${y}`;
}

/** Whether a code unit is a JS whitespace character (the \s set), as a table lookup. */
const WS = new Uint8Array(65536);
for (const c of [9, 10, 11, 12, 13, 32, 160, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff]) WS[c] = 1;
for (let c = 0x2000; c <= 0x200a; c++) WS[c] = 1;

/** The words of a body: its runs of characters other than whitespace (what /\S+/g counts). */
function wordsOf(text) {
  let n = 0;
  let inWord = false;
  for (let i = 0; i < text.length; i++) {
    if (WS[text.charCodeAt(i)]) inWord = false;
    else if (!inWord) {
      inWord = true;
      n++;
    }
  }
  return n;
}

// ---------------------------------------------------------------- front matter

const KEYS = ['title', 'date', 'tags', 'draft', 'layout', 'slug', 'summary'];
const LINE_RE = /^([a-z_]+):(?: (.*))?$/;
const DATE_RE = /^(\d{4})-(\d{2})-(\d{2})$/;
const NAME_RE = /^[a-z0-9-]+$/;
const SLUG_RE = /^[a-z0-9]+(?:-[a-z0-9]+)*$/;
const TAG_RE = /^[^"[\]]+$/;

/** The days of month `m` (1-12) of year `y`, by the Gregorian rule. */
function daysIn(y, m) {
  if (m === 2) return (y % 4 === 0 && y % 100 !== 0) || y % 400 === 0 ? 29 : 28;
  return m === 4 || m === 6 || m === 9 || m === 11 ? 30 : 31;
}

/** A string value: "..." with \" and \\ its only escapes, or bare, the rest of the line (never opening on " or [). */
function stringOf(raw) {
  if (raw.startsWith('"')) {
    if (raw.length < 2 || !raw.endsWith('"')) return { error: 'a quoted string is not closed' };
    let out = '';
    for (let i = 1; i < raw.length - 1; i++) {
      const c = raw[i];
      if (c === '\\') {
        const n = raw[i + 1];
        if ((n !== '"' && n !== '\\') || i + 1 === raw.length - 1) return { error: 'a quoted string holds an escape other than \\" or \\\\' };
        out += n;
        i++;
      } else if (c === '"') return { error: 'a quoted string holds a stray quote' };
      else out += c;
    }
    return { value: out };
  }
  if (raw.startsWith('[')) return { error: 'a bare string opens on [' };
  return { value: raw };
}

/** One key's value, or why it is refused. */
function valueOf(key, raw) {
  switch (key) {
    case 'title':
    case 'summary': {
      const s = stringOf(raw);
      return 'error' in s ? { error: `key "${key}": ${s.error}` } : s;
    }
    case 'date': {
      const m = DATE_RE.exec(raw);
      const y = m ? Number(m[1]) : 0;
      const mo = m ? Number(m[2]) : 0;
      const d = m ? Number(m[3]) : 0;
      if (!m || y < 1970 || y > 2099 || mo < 1 || mo > 12 || d < 1 || d > daysIn(y, mo)) return { error: 'key "date": not a date from 1970-01-01 to 2099-12-31 (YYYY-MM-DD)' };
      return { value: raw };
    }
    case 'tags': {
      if (!raw.startsWith('[') || !raw.endsWith(']')) return { error: 'key "tags": not a list [a, b]' };
      const inner = raw.slice(1, -1);
      if (inner.trim() === '') return { value: [] };
      const tags = inner.split(',').map((t) => t.trim());
      if (tags.some((t) => t === '' || !TAG_RE.test(t))) return { error: 'key "tags": an empty tag, or one holding " [ or ]' };
      return { value: tags };
    }
    case 'draft':
      return raw === 'true' ? { value: true } : raw === 'false' ? { value: false } : { error: 'key "draft": true or false' };
    case 'layout':
      return NAME_RE.test(raw) ? { value: raw } : { error: 'key "layout": not a template name' };
    case 'slug':
      return SLUG_RE.test(raw) && raw.length <= 64 ? { value: raw } : { error: 'key "slug": not a slug' };
    default:
      return { error: `unknown key "${key}"` };
  }
}

/**
 * A source's front matter and body: { data, body }, or { error } with the first reason it is refused.
 * `text` has "\n" line ends. The closing line is found by index, and only the front-matter lines
 * are split out; the body is sliced, never split and re-joined.
 */
function parseFrontMatter(text) {
  const nl = text.indexOf('\n');
  if ((nl === -1 ? text : text.slice(0, nl)) !== '---') return { error: 'no front matter' };
  if (nl === -1) return { error: 'the front matter is not closed' };
  let closeStart = -1;
  let closeEnd = -1;
  let from = nl;
  for (;;) {
    const idx = text.indexOf('\n---', from);
    if (idx === -1) break;
    const after = idx + 4;
    if (after === text.length || text[after] === '\n') {
      closeStart = idx + 1;
      closeEnd = after === text.length ? text.length : after + 1;
      break;
    }
    from = idx + 1;
  }
  if (closeStart === -1) return { error: 'the front matter is not closed' };
  const data = {};
  const fmLines = text.slice(nl + 1, closeStart).split('\n');
  for (let k = 0; k < fmLines.length; k++) {
    const line = fmLines[k];
    if (/^[ \t]*$/.test(line) || line.startsWith('#')) continue;
    const m = LINE_RE.exec(line);
    if (!m) return { error: `line ${k + 2} is not "key: value"` };
    const key = m[1];
    const raw = (m[2] ?? '').replace(/[ \t]+$/, '');
    if (!KEYS.includes(key)) return { error: `unknown key "${key}"` };
    if (Object.hasOwn(data, key)) return { error: `key "${key}" is given twice` };
    if (raw === '') return { error: `key "${key}" has no value` };
    const v = valueOf(key, raw);
    if ('error' in v) return v;
    data[key] = v.value;
  }
  if (!Object.hasOwn(data, 'title')) return { error: 'no title' };
  return { data, body: text.slice(closeEnd) };
}

// ---------------------------------------------------------------- markdown

/** Whether `s` is only spaces and tabs (a blank line). */
function onlySpacesTabs(s) {
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (c !== ' ' && c !== '\t') return false;
  }
  return true;
}

/** Whether the characters of `s` from `a` to `b` are only spaces and tabs. */
function onlySpacesTabsRange(s, a, b) {
  for (let i = a; i < b; i++) {
    const c = s[i];
    if (c !== ' ' && c !== '\t') return false;
  }
  return true;
}

/** A line with its leading and trailing spaces and tabs dropped. */
function trimLine(line) {
  let a = 0;
  let b = line.length;
  while (a < b && (line[a] === ' ' || line[a] === '\t')) a++;
  while (b > a && (line[b - 1] === ' ' || line[b - 1] === '\t')) b--;
  return a === 0 && b === line.length ? line : line.slice(a, b);
}

/** Whether a line is a fence opening (``` plus a language of [A-Za-z0-9_+-]*, then only spaces and tabs); the language, or null. */
function fenceLang(line) {
  if (!line.startsWith('```')) return null;
  let j = 3;
  while (j < line.length) {
    const c = line[j];
    if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c === '_' || c === '+' || c === '-') j++;
    else break;
  }
  return onlySpacesTabsRange(line, j, line.length) ? line.slice(3, j) : null;
}

/** Whether a line is a fence closing (``` then only spaces and tabs). */
function fenceClose(line) {
  return line.startsWith('```') && onlySpacesTabsRange(line, 3, line.length);
}

/** A heading's depth and text (a run of 1-6 #s, then spaces or tabs, then text that is not empty once trailing spaces and tabs are dropped), or null. */
function headingOf(line) {
  let n = 0;
  while (n < line.length && line[n] === '#') n++;
  if (n === 0 || n > 6) return null;
  if (line[n] !== ' ' && line[n] !== '\t') return null;
  let j = n;
  while (j < line.length && (line[j] === ' ' || line[j] === '\t')) j++;
  let end = line.length;
  while (end > j && (line[end - 1] === ' ' || line[end - 1] === '\t')) end--;
  if (end === j) return null;
  return { depth: n, text: line.slice(j, end) };
}

/** Whether a line is a thematic break (--- or ***, then only spaces and tabs). */
function isHr(line) {
  return (line.startsWith('---') || line.startsWith('***')) && onlySpacesTabsRange(line, 3, line.length);
}

/** A list item's start number and text (1-9 digits, ". ", then text), or null. */
function orderedOf(line) {
  let d = 0;
  while (d < line.length && line[d] >= '0' && line[d] <= '9') d++;
  if (d === 0 || d > 9) return null;
  if (line[d] !== '.' || line[d + 1] !== ' ') return null;
  return { start: Number(line.slice(0, d)), text: line.slice(d + 2) };
}

/** Whether a line continues a list item (2 or more spaces, then a character that is not whitespace). */
function continued(line) {
  let n = 0;
  while (n < line.length && line[n] === ' ') n++;
  return n >= 2 && n < line.length && !WS[line.charCodeAt(n)];
}

/** Whether a line ends a paragraph: blank, a fence opening, a heading, or a thematic break. */
function endsParagraph(line) {
  if (line === '') return true;
  const c = line[0];
  if (c === ' ' || c === '\t') return onlySpacesTabs(line);
  if (c === '`') return fenceLang(line) !== null;
  if (c === '#') return headingOf(line) !== null;
  if (c === '-' || c === '*') return isHr(line);
  return false;
}

/**
 * A source's blocks: { type, ... } for code, heading, hr, blockquote, list and paragraph.
 * Lines are dispatched on their first character; a paragraph absorbs every line until a blank
 * line, fence, heading or thematic break.
 */
function lex(src) {
  const lines = src.split('\n');
  const tokens = [];
  let i = 0;
  while (i < lines.length) {
    const line = lines[i];
    if (line === '' || (line[0] === ' ' || line[0] === '\t') && onlySpacesTabs(line)) {
      i++;
      continue;
    }
    const c = line[0];
    if (c === '`') {
      const lang = fenceLang(line);
      if (lang !== null) {
        const body = [];
        i++;
        while (i < lines.length && !fenceClose(lines[i])) body.push(lines[i++]);
        i++;
        tokens.push({ type: 'code', lang, lines: body });
        continue;
      }
    } else if (c === '#') {
      const h = headingOf(line);
      if (h !== null) {
        tokens.push({ type: 'heading', depth: h.depth, text: h.text });
        i++;
        continue;
      }
    } else if (c === '-' || c === '*') {
      if (isHr(line)) {
        tokens.push({ type: 'hr' });
        i++;
        continue;
      }
      if (line[1] === ' ') {
        const isOrdered = false;
        const items = [[trimLine(line.slice(2))]];
        i++;
        while (i < lines.length) {
          const m = lines[i];
          if ((m[0] === '-' || m[0] === '*') && m[1] === ' ') {
            items.push([trimLine(m.slice(2))]);
            i++;
          } else if (continued(m)) {
            items[items.length - 1].push(trimLine(m));
            i++;
          } else break;
        }
        tokens.push({ type: 'list', ordered: isOrdered, start: 1, items: items.map((parts) => parts.join('\n')) });
        continue;
      }
    } else if (c === '>') {
      const body = [];
      while (i < lines.length && lines[i][0] === '>') {
        const l = lines[i];
        body.push(l[1] === ' ' ? l.slice(2) : l.slice(1));
        i++;
      }
      tokens.push({ type: 'blockquote', lines: body.map(trimLine).filter((l) => l !== '') });
      continue;
    } else if (c >= '0' && c <= '9') {
      const o = orderedOf(line);
      if (o !== null) {
        const items = [[trimLine(o.text)]];
        const start = o.start;
        i++;
        while (i < lines.length) {
          const m = lines[i];
          const o2 = orderedOf(m);
          if (o2 !== null) {
            items.push([trimLine(o2.text)]);
            i++;
          } else if (continued(m)) {
            items[items.length - 1].push(trimLine(m));
            i++;
          } else break;
        }
        tokens.push({ type: 'list', ordered: true, start, items: items.map((parts) => parts.join('\n')) });
        continue;
      }
    }
    const body = [trimLine(line)];
    i++;
    while (i < lines.length && !endsParagraph(lines[i])) body.push(trimLine(lines[i++]));
    tokens.push({ type: 'paragraph', text: body.join('\n') });
  }
  return tokens;
}

// ---------------------------------------------------------------- inline

/** The characters a backslash escapes in inline text. */
const ESCAPABLE = new Set(['\\', '`', '*', '_', '[', ']', '(', ')', '#', '+', '-', '.', '!', '>']);

/** The next character of \ ` * [ at or after `from`, or -1. */
function nextSpecial(s, from) {
  let j = -1;
  let a = s.indexOf('\\', from);
  if (a !== -1) j = a;
  a = s.indexOf('`', from);
  if (a !== -1 && (j === -1 || a < j)) j = a;
  a = s.indexOf('*', from);
  if (a !== -1 && (j === -1 || a < j)) j = a;
  a = s.indexOf('[', from);
  if (a !== -1 && (j === -1 || a < j)) j = a;
  return j;
}

/**
 * The first unescaped `what` at or after `from` (-1 when there is none), where a backslash
 * escapes only the characters in ESCAPABLE. With no backslash at all this is indexOf.
 */
function findUnescaped(s, what, from) {
  if (s.indexOf('\\', from) === -1) return s.indexOf(what, from);
  for (let j = from; j <= s.length - what.length; j++) {
    if (s[j] === '\\' && j + 1 < s.length && ESCAPABLE.has(s[j + 1])) {
      j++;
      continue;
    }
    if (s.startsWith(what, j)) return j;
  }
  return -1;
}

/**
 * The first single `*` at or after `from` that is not beside another `*` and not escaped (-1 when there is none).
 * A `*` beside another `*` is skipped with the pair.
 */
function findSingleStar(s, from) {
  if (s.indexOf('\\', from) === -1) {
    let p = s.indexOf('*', from);
    while (p !== -1) {
      if (s[p + 1] === '*') {
        p = s.indexOf('*', p + 2);
        continue;
      }
      return p;
    }
    return -1;
  }
  for (let j = from; j < s.length; j++) {
    const c = s[j];
    if (c === '\\' && j + 1 < s.length && ESCAPABLE.has(s[j + 1])) {
      j++;
      continue;
    }
    if (c !== '*') continue;
    if (s[j + 1] === '*') {
      j++;
      continue;
    }
    return j;
  }
  return -1;
}

/**
 * A paragraph or heading's inline marks, left to right: a backslash before one of \ ` * _ [] () # + -.! >
 * writes that character; a backtick span is <code> to the next backtick; ** is <strong> to the next
 * unescaped **; a single * is <em> to the next single * that is not beside another *; [text](target)
 * is a link when target is not empty and holds no whitespace; every other character is escaped.
 * Plain runs between marks are escaped in bulk.
 */
function inline(s, env) {
  let out = '';
  let i = 0;
  while (i < s.length) {
    const j = nextSpecial(s, i);
    if (j === -1) {
      out += escapeHtml(s.slice(i));
      break;
    }
    if (j > i) out += escapeHtml(s.slice(i, j));
    const c = s[j];
    if (c === '\\') {
      if (j + 1 < s.length && ESCAPABLE.has(s[j + 1])) {
        out += s[j + 1];
        i = j + 2;
      } else {
        out += '\\';
        i = j + 1;
      }
      continue;
    }
    if (c === '`') {
      const k = s.indexOf('`', j + 1);
      if (k > j + 1) {
        out += `<code>${escapeHtml(s.slice(j + 1, k))}</code>`;
        i = k + 1;
      } else {
        out += '`';
        i = j + 1;
      }
      continue;
    }
    if (c === '*') {
      if (s[j + 1] === '*') {
        const k = findUnescaped(s, '**', j + 2);
        if (k > j + 2) {
          out += `<strong>${inline(s.slice(j + 2, k), env)}</strong>`;
          i = k + 2;
        } else {
          out += '**';
          i = j + 2;
        }
        continue;
      }
      const k = findSingleStar(s, j + 1);
      if (k > j + 1) {
        out += `<em>${inline(s.slice(j + 1, k), env)}</em>`;
        i = k + 1;
      } else {
        out += '*';
        i = j + 1;
      }
      continue;
    }
    const k = findUnescaped(s, ']', j + 1);
    const m = k !== -1 && s[k + 1] === '(' ? s.indexOf(')', k + 2) : -1;
    const target = m === -1 ? '' : s.slice(k + 2, m);
    if (target !== '' && !/\s/.test(target)) {
      out += `<a href="${escapeHtml(env.link(target))}">${inline(s.slice(j + 1, k), env)}</a>`;
      i = m + 1;
      continue;
    }
    out += '[';
    i = j + 1;
  }
  return out;
}

/**
 * A source's body as HTML: { html, toc, excerpt }. Heading ids are unique per source (slug, slug-2 ...);
 * toc holds its level 2 and 3 headings; excerpt is the HTML of its first paragraph, or "".
 */
function renderMarkdown(src, env, slugMemo) {
  const ids = new Set();
  const blocks = [];
  const toc = [];
  let excerpt = null;
  for (const t of lex(src)) {
    switch (t.type) {
      case 'heading': {
        const id = uniqueSlug(slugify(t.text, slugMemo), ids);
        const html = inline(t.text, env);
        blocks.push(`<h${t.depth} id="${id}">${html}</h${t.depth}>`);
        if (t.depth === 2 || t.depth === 3) toc.push({ level: t.depth, id, html });
        break;
      }
      case 'code': {
        const cls = t.lang === '' ? '' : ` class="language-${escapeHtml(t.lang)}"`;
        blocks.push(`<pre><code${cls}>${t.lines.length === 0 ? '' : `${escapeHtml(t.lines.join('\n'))}\n`}</code></pre>`);
        break;
      }
      case 'hr':
        blocks.push('<hr>');
        break;
      case 'blockquote':
        blocks.push(t.lines.length === 0 ? '<blockquote>\n</blockquote>' : `<blockquote>\n<p>${inline(t.lines.join('\n'), env)}</p>\n</blockquote>`);
        break;
      case 'list': {
        const tag = t.ordered ? 'ol' : 'ul';
        const open = t.ordered && t.start !== 1 ? `<ol start="${t.start}">` : `<${tag}>`;
        blocks.push(`${open}\n${t.items.map((item) => `<li>${inline(item, env)}</li>\n`).join('')}</${tag}>`);
        break;
      }
      case 'paragraph': {
        const html = inline(t.text, env);
        if (excerpt === null) excerpt = html;
        blocks.push(`<p>${html}</p>`);
        break;
      }
    }
  }
  return { html: blocks.length === 0 ? '' : `${blocks.join('\n')}\n`, toc, excerpt: excerpt ?? '' };
}

// ---------------------------------------------------------------- templates

class TemplateError extends Error {}

/** A template's path: names of [A-Za-z_][A-Za-z0-9_]* joined by ".", or why it is not one. */
function pathOf(name, text) {
  const path = text.split('.');
  const ok = path.length > 0 && path.every((name) => /^[A-Za-z_][A-Za-z0-9_]*$/.test(name));
  if (!ok) throw new TemplateError(`template "${name}": ${JSON.stringify(text)} is not a path`);
  return path;
}

/**
 * A template's tokens: { text } or { var: path, raw } or { tag }.
 * {{ }} is a variable, {{{ }}} its raw form, {% %} a tag. A {% %} tag alone on its line (only
 * spaces and tabs beside it) takes the whole line with it, \n included.
 */
function tokenize(name, src) {
  const tokens = [];
  let text = '';
  let i = 0;
  while (i < src.length) {
    const open = src.indexOf('{', i);
    if (open === -1 || open === src.length - 1) {
      text += src.slice(i);
      break;
    }
    const next = src[open + 1];
    if (next !== '{' && next !== '%') {
      text += src.slice(i, open + 1);
      i = open + 1;
      continue;
    }
    text += src.slice(i, open);
    if (next === '{') {
      const raw = src[open + 2] === '{';
      const close = src.indexOf(raw ? '}}}' : '}}', open + (raw ? 3 : 2));
      if (close === -1) throw new TemplateError(`template "${name}": a ${raw ? '{{{' : '{{'} is not closed`);
      if (text !== '') tokens.push({ text });
      text = '';
      tokens.push({ var: pathOf(name, src.slice(open + (raw ? 3 : 2), close).trim()), raw });
      i = close + (raw ? 3 : 2);
    } else {
      const close = src.indexOf('%}', open + 2);
      if (close === -1) throw new TemplateError(`template "${name}": a {% is not closed`);
      const end = close + 2;
      const lineStart = src.lastIndexOf('\n', open - 1) + 1;
      const nl = src.indexOf('\n', end);
      const lineEnd = nl === -1 ? src.length : nl;
      const standalone = onlySpacesTabsRange(src, lineStart, open) && onlySpacesTabsRange(src, end, lineEnd);
      if (standalone) text = text.slice(0, text.length - (open - lineStart));
      if (text !== '') tokens.push({ text });
      text = '';
      tokens.push({ tag: src.slice(open + 2, close).trim() });
      i = standalone ? (nl === -1 ? src.length : nl + 1) : end;
    }
  }
  if (text !== '') tokens.push({ text });
  return tokens;
}

const FOR_RE = /^for ([A-Za-z_][A-Za-z0-9_]*) in (\S+)$/;
const IF_RE = /^if (not )?(\S+)$/;
const INCLUDE_RE = /^include "([a-z0-9-]+)"$/;

/**
 * A template's node tree. A path's first name is read from the innermost loop binding it (loop
 * before the element), else from the page's values; each next name is an own property of the
 * value so far, or undefined.
 */
function parseTemplate(name, src) {
  const root = { kind: 'root', body: [] };
  const stack = [root];
  let body = root.body;
  for (const tok of tokenize(name, src)) {
    if ('tag' in tok) {
      const tag = tok.tag;
      const top = stack[stack.length - 1];
      const forMatch = FOR_RE.exec(tag);
      if (forMatch) {
        const node = { kind: 'for', name: forMatch[1], path: pathOf(name, forMatch[2]), body: [] };
        body.push(node);
        stack.push(node);
        body = node.body;
        continue;
      }
      const ifMatch = IF_RE.exec(tag);
      if (ifMatch) {
        const node = { kind: 'if', path: pathOf(name, ifMatch[2]), not: ifMatch[1] === 'not ', then: [], else: null };
        body.push(node);
        stack.push(node);
        body = node.then;
        continue;
      }
      const includeMatch = INCLUDE_RE.exec(tag);
      if (includeMatch) {
        body.push({ kind: 'include', name: includeMatch[1] });
        continue;
      }
      if (tag === 'else') {
        if (top.kind !== 'if' || top.else !== null) throw new TemplateError(`template "${name}": an else has no if, or an if has two elses`);
        top.else = [];
        body = top.else;
        continue;
      }
      if (tag === 'endfor' || tag === 'endif') {
        if (top.kind !== (tag === 'endfor' ? 'for' : 'if')) throw new TemplateError(`template "${name}": an ${tag} closes nothing, or the wrong thing`);
        stack.pop();
        const parent = stack[stack.length - 1];
        body = parent.kind === 'root' ? parent.body : parent.kind === 'for' ? parent.body : parent.else ?? parent.then;
        continue;
      }
      throw new TemplateError(`template "${name}": ${JSON.stringify(tag)} is not a tag`);
    }
    body.push(tok);
  }
  if (stack.length > 1) throw new TemplateError(`template "${name}": a ${stack[stack.length - 1].kind} is not closed`);
  return root.body;
}

/** A path's value in a scope, or undefined. */
function lookup(scope, path) {
  let s = scope;
  let v;
  while (s !== null && !Object.hasOwn(s.vars, path[0])) s = s.parent;
  if (s === null) return undefined;
  v = s.vars[path[0]];
  for (let k = 1; k < path.length; k++) {
    if (v === null || typeof v !== 'object' || !Object.hasOwn(v, path[k])) return undefined;
    v = v[path[k]];
  }
  return v;
}

/** A value as text: a string itself, a number in JavaScript's digits, true/false, an array as its items written joined by ", ", anything else "". */
function textOf(v) {
  if (typeof v === 'string') return v;
  if (typeof v === 'number') return String(v);
  if (typeof v === 'boolean') return v ? 'true' : 'false';
  if (Array.isArray(v)) return v.map(textOf).join(', ');
  return '';
}

/** Whether a value counts as true for {% if %}: anything but undefined, null, false, "", 0 or an empty array. */
function truthy(v) {
  if (Array.isArray(v)) return v.length > 0;
  return v !== undefined && v !== null && v !== false && v !== '' && v !== 0;
}

/**
 * A node tree as text. For renders the body of each array element, with the element and loop
 * (index from 1, first, last, length) bound in a scope of its own. If renders the then branch, or
 * the else branch when there is one. Include renders the named template in the same scope, up to
 * 8 deep; a missing one renders nothing.
 */
function renderNodes(nodes, scope, ctx, depth) {
  let out = '';
  for (const node of nodes) {
    if ('text' in node) {
      out += node.text;
      continue;
    }
    if ('var' in node) {
      const v = textOf(lookup(scope, node.var));
      out += node.raw ? v : ctx.escape(v);
      continue;
    }
    if (node.kind === 'if') {
      const branch = truthy(lookup(scope, node.path)) !== node.not ? node.then : node.else;
      if (branch !== null) out += renderNodes(branch, scope, ctx, depth);
      continue;
    }
    if (node.kind === 'for') {
      const xs = lookup(scope, node.path);
      if (Array.isArray(xs)) {
        for (let k = 0; k < xs.length; k++) {
          const vars = { [node.name]: xs[k], loop: { index: k + 1, first: k === 0, last: k === xs.length - 1, length: xs.length } };
          out += renderNodes(node.body, { vars, parent: scope }, ctx, depth);
        }
      }
      continue;
    }
    const t = ctx.templates.get(node.name);
    if (t !== undefined && depth < 8) out += renderNodes(t, scope, ctx, depth + 1);
  }
  return out;
}

// ---------------------------------------------------------------- build

/** A relative path from a source's directory: "." and ".." steps resolved, never above the root (null when it climbs above it). */
function resolvePath(dir, rel) {
  const parts = dir === '' ? [] : dir.split('/');
  for (const seg of rel.split('/')) {
    if (seg === '' || seg === '.') continue;
    if (seg === '..') {
      if (parts.length === 0) return null;
      parts.pop();
    } else parts.push(seg);
  }
  return parts.join('/');
}

function readSources(b) {
  const files = [...b.input.files].sort((x, y) => byCodeUnits(x.path, y.path));
  for (const f of files) {
    if (f.path.endsWith('.md')) {
      b.sources.push({ path: f.path, text: f.content.indexOf('\r') === -1 ? f.content : f.content.replace(/\r\n?/g, '\n') });
    } else b.statics.push({ path: f.path, content: f.content });
  }
}

function frontMatterStep(b) {
  const kept = [];
  for (const s of b.sources) {
    const fm = parseFrontMatter(s.text);
    if ('error' in fm) {
      b.report.push(`refused ${s.path}: ${fm.error}`);
      continue;
    }
    s.data = fm.data;
    s.body = fm.body;
    s.post = s.path.startsWith('posts/');
    const own = RESERVED.find((d) => d !== 'posts' && s.path.startsWith(`${d}/`));
    if (own !== undefined) {
      b.report.push(`refused ${s.path}: ${own}/ is the generator's own`);
      continue;
    }
    if (s.post && !Object.hasOwn(s.data, 'date')) {
      b.report.push(`refused ${s.path}: a post needs a date`);
      continue;
    }
    const layout = s.data.layout ?? (s.post ? 'post' : 'page');
    if (!b.templates.has(layout)) {
      b.report.push(`refused ${s.path}: layout "${layout}" is no template that parses`);
      continue;
    }
    s.layout = layout;
    if (s.data.draft === true) {
      b.report.push(`draft ${s.path}`);
      continue;
    }
    kept.push(s);
  }
  b.sources = kept;
}

function permalinksStep(b) {
  const taken = new Map();
  const takenIn = (dir) => {
    let set = taken.get(dir);
    if (set === undefined) {
      set = new Set(dir === '' ? RESERVED : []);
      taken.set(dir, set);
    }
    return set;
  };
  for (const s of b.sources) {
    const dir = s.post ? 'posts' : dirOf(s.path);
    const slug = uniqueSlug(s.data.slug ?? slugify(s.data.title, b.slugMemo), takenIn(dir));
    s.slug = slug;
    s.outDir = dir === '' ? slug : `${dir}/${slug}`;
    s.url = `${b.base}/${s.outDir}/`;
    b.bySource.set(s.path, s);
  }
}

function markdownStep(b) {
  const staticPaths = new Set(b.statics.map((f) => f.path));
  for (const s of b.sources) {
    const dir = dirOf(s.path);
    const env = {
      link: (target) => {
        if (/^[A-Za-z][A-Za-z0-9+.-]*:/.test(target) || target.startsWith('/') || target.startsWith('#')) return target;
        const key = `${dir}\n${target}`;
        const cached = b.linkCache.get(key);
        if (cached !== undefined) {
          if (cached === null) b.broken.add(`broken-link ${s.path} -> ${target}`);
          return cached === null ? target : cached;
        }
        const hash = target.indexOf('#');
        const rel = hash === -1 ? target : target.slice(0, hash);
        const frag = hash === -1 ? '' : target.slice(hash);
        const path = rel === '' ? null : resolvePath(dir, rel);
        let href = null;
        if (path !== null && b.bySource.has(path)) href = `${b.bySource.get(path).url}${frag}`;
        else if (path !== null && staticPaths.has(path)) href = `${b.base}/${path}${frag}`;
        if (href === null) {
          b.linkCache.set(key, null);
          b.broken.add(`broken-link ${s.path} -> ${target}`);
          return target;
        }
        b.linkCache.set(key, href);
        return href;
      },
    };
    const md = renderMarkdown(s.body, env, b.slugMemo);
    s.html = md.html;
    s.toc = md.toc;
    s.excerpt = md.excerpt;
  }
}

function collectionsStep(b) {
  const posts = b.sources.filter((s) => s.post);
  posts.sort((x, y) => byCodeUnits(y.data.date, x.data.date) || byCodeUnits(x.slug, y.slug));
  b.posts = posts;
  posts.forEach((p, k) => {
    p.newer = k === 0 ? null : posts[k - 1];
    p.older = k === posts.length - 1 ? null : posts[k + 1];
  });
}

function tagsStep(b) {
  const bySlug = new Map();
  const ownTags = (s) => {
    const seen = new Set();
    const out = [];
    for (const name of s.data.tags ?? []) {
      const slug = slugify(name, b.slugMemo);
      if (seen.has(slug)) continue;
      seen.add(slug);
      out.push({ name, slug });
    }
    return out;
  };
  for (const p of b.posts) {
    p.tagRefs = [];
    for (const t of ownTags(p)) {
      let tag = bySlug.get(t.slug);
      if (tag === undefined) {
        tag = { name: t.name, slug: t.slug, url: `${b.base}/tags/${t.slug}/`, posts: [] };
        bySlug.set(t.slug, tag);
      }
      tag.posts.push(p);
      p.tagRefs.push(tag);
    }
  }
  for (const s of b.sources) {
    if (s.post) continue;
    s.tagRefs = ownTags(s).map((t) => bySlug.get(t.slug) ?? { name: t.name, slug: t.slug, url: '', posts: [] });
  }
  b.tags = [...bySlug.values()].sort((x, y) => y.posts.length - x.posts.length || byCodeUnits(x.slug, y.slug));
}

/** A post or page as a card: title, url, date and date_long, summary, excerpt, reading minutes, tags. */
function cardOf(b, s) {
  return {
    title: s.data.title,
    url: s.url,
    date: s.data.date ?? '',
    date_long: s.data.date === undefined ? '' : longDate(s.data.date),
    summary: s.data.summary ?? '',
    excerpt: s.excerpt,
    reading_minutes: Math.max(1, Math.ceil(wordsOf(s.body) / 200)),
    tags: s.tagRefs.map((t) => ({ name: t.name, slug: t.slug, url: t.url })),
  };
}

/** A neighbouring post or page as a link: title, url, date and date_long, or null. */
function linkOf(s) {
  return s === null ? null : { title: s.data.title, url: s.url, date: s.data.date ?? '', date_long: s.data.date === undefined ? '' : longDate(s.data.date) };
}

/** A post or page as a page: its card, slug, content, table of contents, newer and older links, is_post. A post reuses the card its collection already built. */
function pageOf(b, s) {
  const card = s.post ? b.cards.get(s) : cardOf(b, s);
  return {
    ...card,
    slug: s.slug,
    content: s.html,
    toc: s.toc.map((h) => ({ level: h.level, id: h.id, html: h.html })),
    newer: linkOf(s.newer ?? null),
    older: linkOf(s.older ?? null),
    is_post: s.post,
  };
}

/** A tag as a page sees it: name, slug, url, count, posts as cards. */
function tagOf(b, t) {
  return { name: t.name, slug: t.slug, url: t.url, count: t.posts.length, posts: t.posts.map((p) => b.cards.get(p)) };
}

function layoutsStep(b) {
  b.cards = new Map(b.posts.map((p) => [p, cardOf(b, p)]));
  const site = { title: b.input.site.title, base_url: b.base };
  const allTags = b.tags.map((t) => ({ name: t.name, slug: t.slug, url: t.url, count: t.posts.length }));
  const recent = b.posts.slice(0, b.input.site.recent).map((p) => b.cards.get(p));
  const rootScope = { vars: { site, tags: allTags, recent }, parent: null };
  const ctx = { templates: b.templates, escape: escapeHtml };
  const render = (name, vars) => {
    const nodes = b.templates.get(name);
    return nodes === undefined ? null : renderNodes(nodes, { vars, parent: rootScope }, ctx, 0);
  };
  for (const s of b.sources) b.output[`${s.outDir}/index.html`] = render(s.layout, { page: pageOf(b, s) });
  const per = b.input.site.per_page;
  const pages = Math.max(1, Math.ceil(b.posts.length / per));
  const indexUrl = (k) => (k === 1 ? `${b.base}/` : `${b.base}/page/${k}/`);
  for (let k = 1; k <= pages; k++) {
    const html = render('index', {
      posts: b.posts.slice((k - 1) * per, k * per).map((p) => b.cards.get(p)),
      pager: { number: k, total: pages, url: indexUrl(k), newer_url: k === 1 ? '' : indexUrl(k - 1), older_url: k === pages ? '' : indexUrl(k + 1) },
    });
    if (html !== null) b.output[k === 1 ? 'index.html' : `page/${k}/index.html`] = html;
  }
  for (const t of b.tags) {
    const html = render('tag', { tag: tagOf(b, t) });
    if (html !== null) b.output[`tags/${t.slug}/index.html`] = html;
  }
  const tagsHtml = render('tags', {});
  if (tagsHtml !== null) b.output['tags/index.html'] = tagsHtml;
  for (const f of b.statics) {
    if (Object.hasOwn(b.output, f.path)) b.report.push(`shadowed ${f.path}: a built page has its path`);
    else b.output[f.path] = f.content;
  }
}

function reportStep(b) {
  const lines = [...b.report, ...b.broken].sort(byCodeUnits);
  const pages = b.sources.filter((s) => !s.post).length;
  lines.push(`built ${pages} pages, ${b.posts.length} posts, ${b.tags.length} tags and ${b.statics.length} static files`);
  b.output[REPORT_FILE] = `${lines.join('\n')}\n`;
}

/** Build `input` into the tree of paths and file contents: the output of one case. */
function build(input) {
  const b = {
    input,
    base: input.site.base_url.replace(/\/+$/, ''),
    templates: new Map(),
    sources: [],
    statics: [],
    bySource: new Map(),
    broken: new Set(),
    report: [],
    posts: [],
    tags: [],
    cards: new Map(),
    output: {},
    slugMemo: new Map(),
    linkCache: new Map(),
  };
  for (const name of Object.keys(input.templates).sort(byCodeUnits)) {
    try {
      b.templates.set(name, parseTemplate(name, input.templates[name]));
    } catch (err) {
      if (!(err instanceof TemplateError)) throw err;
      b.report.push(err.message);
    }
  }
  readSources(b);
  frontMatterStep(b);
  permalinksStep(b);
  markdownStep(b);
  collectionsStep(b);
  tagsStep(b);
  layoutsStep(b);
  reportStep(b);
  return b.output;
}

export function run(input) {
  return build(input);
}
