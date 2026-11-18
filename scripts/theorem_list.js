#!/usr/bin/env node
// Write the full theorem list of EntropyLean/ as Markdown (docs/THEOREMS.md).
//
// Usage:  node scripts/theorem_list.js [commit] > docs/THEOREMS.md
//
// Every `theorem` and `lemma` of `EntropyLean/*.lean` is listed by file, with its
// namespace-qualified name, the first paragraph of its docstring and a link to its source line.
// `commit` (default: the output of `git rev-parse HEAD`, else `main`) is the commit the links
// point at. Declarations whose proof still contains `sorry` are marked. `FeatureMap.lean` is a
// separate project and is not listed.
//
// The function `theoremList(files, commit)` is pure (files: [{name, text}]), so the same code
// also runs in a browser page.
"use strict";

const REPO = "https://github.com/JosiahPark/entropy-quotients-lean";
const SKIP = new Set(["FeatureMap.lean"]);

const MODS = "(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\\s+)*";
const ATTR = "(?:@\\[[^\\]\\n]*\\]\\s*)?";
const DECL = new RegExp("^" + ATTR + MODS +
  "(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|example|opaque|axiom|end" +
  "|section|namespace|variable|open|omit|universe|attribute|set_option|include|#\\w+)\\b");
const THM = new RegExp("^" + ATTR + MODS + "(?:theorem|lemma)\\s+([^\\s:({\\[]+)");
const NAMESPACE = /^namespace\s+(\S+)/;
const SECTION = /^(?:noncomputable\s+)?section\b\s*(\S*)/;
const END = /^end\b\s*(\S*)/;
const SORRY = /\bsorry\b/;
const BETWEEN = /^(open .* in|omit .* in|include .* in)$/;

const count = (s, ch) => s.split(ch).length - 1;

// Blank out comments, keeping the line structure. Returns the code lines and the docstrings,
// keyed by the index of the line on which each docstring ends.
function stripComments(text) {
  const out = [], docs = new Map(), n = text.length;
  let i = 0, line = 0;
  while (i < n) {
    if (text.startsWith("/-", i)) {
      let depth = 1, j = i + 2;
      while (j < n && depth) {
        if (text.startsWith("/-", j)) { depth++; j += 2; }
        else if (text.startsWith("-/", j)) { depth--; j += 2; }
        else j++;
      }
      const block = text.slice(i, j), nl = count(block, "\n");
      if (block.startsWith("/--")) docs.set(line + nl, block.slice(3, -2).trim());
      out.push("\n".repeat(nl));
      line += nl;
      i = j;
    } else if (text.startsWith("--", i)) {
      const j = text.indexOf("\n", i);
      i = j < 0 ? n : j;
    } else {
      if (text[i] === "\n") line++;
      out.push(text[i]);
      i++;
    }
  }
  return {lines: out.join("").split("\n"), docs};
}

function firstParagraph(doc, limit = 260) {
  let para = doc.split("\n\n")[0].trim().split(/\s+/).join(" ");
  const cps = Array.from(para);
  if (cps.length > limit) {
    let cut = cps.slice(0, limit).join("");
    const k = cut.lastIndexOf(" ");
    if (k >= 0) cut = cut.slice(0, k);
    para = cut + " …";
    if (count(para, "`") % 2) para += "`";
  }
  return para;
}

function titleOf(text) {
  const m = text.match(/\/-!\s*\n?\s*#\s+(.+)/);
  return m ? m[1].trim() : "";
}

function theorems(text) {
  const {lines, docs} = stripComments(text);
  const scope = [], found = [];
  let cur = null, lastDoc = null;
  lines.forEach((line, no) => {
    if (docs.has(no)) lastDoc = [no, docs.get(no)];
    if (DECL.test(line)) {
      if (cur) found.push(cur);
      cur = null;
      const ns = line.match(NAMESPACE), sec = line.match(SECTION), end = line.match(END);
      if (ns) scope.push(["namespace", ns[1]]);
      else if (sec) scope.push(["section", sec[1]]);
      else if (end && scope.length) scope.pop();
      const m = line.match(THM);
      if (m) {
        const prefix = scope.filter(s => s[0] === "namespace").map(s => s[1]).join(".");
        let full = m[1].startsWith("_root_.") ? m[1].slice(7) : prefix ? prefix + "." + m[1] : m[1];
        if (full.startsWith("EntropyLean.")) full = full.slice("EntropyLean.".length);
        // a docstring belongs to this declaration if only blank, attribute or `… in` lines
        // separate them
        let doc = "";
        if (lastDoc && lines.slice(lastDoc[0] + 1, no).every(l => {
          const t = l.trim();
          return !t || t.startsWith("@[") || BETWEEN.test(t);
        })) doc = firstParagraph(lastDoc[1]);
        cur = {name: full, line: no + 1, doc, sorry: SORRY.test(line)};
      } else lastDoc = null;
    } else if (cur && SORRY.test(line)) cur.sorry = true;
  });
  if (cur) found.push(cur);
  return {title: titleOf(text), found};
}

// files: [{name: "Basic.lean", text: "..."}], the files of EntropyLean/.
function theoremList(files, commit) {
  const list = files.filter(f => f.name.endsWith(".lean") && !SKIP.has(f.name))
    .sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0))
    .map(f => Object.assign({name: f.name}, theorems(f.text)));
  const total = list.reduce((n, f) => n + f.found.length, 0);
  const open = [];
  for (const f of list) for (const t of f.found) if (t.sorry) open.push([f.name, t]);
  const short = /^[0-9a-f]{40}$/.test(commit) ? commit.slice(0, 7) : commit;
  const blob = `${REPO}/blob/${commit}/EntropyLean`;
  const out = ["# Theorem list", ""];
  out.push(
    `Every \`theorem\` and \`lemma\` in \`EntropyLean/\`: ${total} declarations in ${list.length} ` +
    `files, at commit [\`${short}\`](${REPO}/commit/${commit}). Each name links to its source line ` +
    "at that commit. Names are relative to the namespace `EntropyLean`; the text after a name is " +
    "the first paragraph of its docstring.");
  out.push("");
  out.push(
    "This file is generated by [`scripts/theorem_list.js`](../scripts/theorem_list.js) " +
    "(`node scripts/theorem_list.js > docs/THEOREMS.md`); regenerate it when the Lean files " +
    "change. Definitions are not listed. `FeatureMap.lean` is a separate project and is not " +
    "listed. What each file proves and does not prove is stated in the docstring at its top; " +
    "[ROADMAP.md](../ROADMAP.md) says which roadmap item wrote each declaration.");
  out.push("");
  if (open.length) {
    out.push(`**${open.length} of the ${total} are statements whose proof is still \`sorry\`**, ` +
      "not proved results:");
    out.push("");
    for (const [fn, t] of open)
      out.push(`- [\`${t.name}\`](${blob}/${fn}#L${t.line}) (\`${fn}\`)` + (t.doc ? `: ${t.doc}` : ""));
  } else out.push(`None of the ${total} contains \`sorry\`.`);
  out.push("", "## Files", "", "| File | Contents | Theorems |", "| --- | --- | ---: |");
  for (const f of list)
    out.push(`| [\`${f.name}\`](#${f.name.slice(0, -5).toLowerCase()}) | ` +
      `${f.title.split("|").join("\\|")} | ${f.found.length} |`);
  for (const f of list) {
    out.push("", `## ${f.name.slice(0, -5)}`, "");
    out.push(`[\`EntropyLean/${f.name}\`](${blob}/${f.name})` + (f.title ? `: ${f.title}.` : "") +
      ` ${f.found.length} theorem${f.found.length !== 1 ? "s" : ""}.`);
    out.push("");
    for (const t of f.found)
      out.push(`- [\`${t.name}\`](${blob}/${f.name}#L${t.line})${t.sorry ? " **(sorry)**" : ""}` +
        (t.doc ? `: ${t.doc}` : ""));
  }
  return out.join("\n") + "\n";
}

if (typeof module !== "undefined" && module.exports) {
  module.exports = {theoremList};
  if (require.main === module) {
    const fs = require("fs"), path = require("path"), cp = require("child_process");
    const root = path.resolve(__dirname, "..");
    let commit = process.argv[2];
    if (!commit) {
      try {
        commit = cp.execSync("git rev-parse HEAD", {cwd: root, stdio: ["ignore", "pipe", "ignore"]})
          .toString().trim();
      } catch (e) { commit = "main"; }
    }
    const dir = path.join(root, "EntropyLean");
    const files = fs.readdirSync(dir).filter(f => f.endsWith(".lean"))
      .map(f => ({name: f, text: fs.readFileSync(path.join(dir, f), "utf8")}));
    process.stdout.write(theoremList(files, commit));
  }
}
