# Token-aware Local-Example detector — the ENGINE of smart-ctor-gate.sh check 6 (see there for WHY).
# A char-level scanner with cross-line state per file, modeling the RELEVANT Rocq lexical rules:
#   - nested (* *) comments (anywhere, including inside attributes);
#   - string literals with Rocq's ACTUAL escape rule — a doubled "" is an escaped quote, backslash
#     is a LITERAL character (multi-line strings supported);
#   - #[ ... ] attribute blocks (multi-line, bracket-nested), whose own embedded strings/comments
#     neither close the block nor contribute to the locality test;
#   - LOCALITY ACCUMULATION: `Local` / `Global` vernaculars and ANY NUMBER of adjacent attribute
#     blocks decorate the next command token; a #[...local...] block (word `local` OUTSIDE its
#     embedded strings) sets pending locality, a non-local attribute PRESERVES it, `Global` clears
#     it, and any ordinary token flushes it.  If the flushing token is `Example` with locality
#     pending, that is a hit.
# DETECTION BOUNDARY (exact): a locality marker whose decoration chain (attributes, whitespace,
# newlines, comments) reaches `Example` with no other intervening token.  Exits 1 iff any hit.
function isword(c) { return c ~ /[A-Za-z0-9_']/ }
FNR == 1 { cdepth = 0; instr = 0; inattr = 0; inastr = 0; adepth = 0; attrtxt = ""; loc = 0 }
{
  line = $0; n = length(line); i = 1
  while (i <= n) {
    c = substr(line, i, 1); c2 = substr(line, i, 2)
    if (cdepth > 0) {                       # comment (top-level or inside an attribute)
      if (c2 == "(*") { cdepth++; i += 2; continue }
      if (c2 == "*)") { cdepth--; i += 2; continue }
      i++; continue
    }
    if (inastr) {                           # string inside an attribute: "" escapes, ] is literal
      if (c == "\"") { if (c2 == "\"\"") { i += 2; continue } inastr = 0 }
      i++; continue
    }
    if (instr) {                            # top-level string: "" escapes, backslash is LITERAL
      if (c == "\"") { if (c2 == "\"\"") { i += 2; continue } instr = 0 }
      i++; continue
    }
    if (inattr) {
      if (c2 == "(*") { cdepth++; i += 2; continue }
      if (c == "\"") { inastr = 1; i++; continue }
      if (c == "[") { adepth++; attrtxt = attrtxt c; i++; continue }
      if (c == "]") {
        adepth--
        if (adepth == 0) {
          inattr = 0
          if (attrtxt ~ /(^|[^A-Za-z0-9_])local([^A-Za-z0-9_]|$)/) loc = 1
          # a non-local attribute PRESERVES pending locality (accumulation)
        } else attrtxt = attrtxt c
        i++; continue
      }
      attrtxt = attrtxt c; i++; continue
    }
    if (c2 == "(*") { cdepth++; i += 2; continue }
    if (c == "\"") { instr = 1; i++; continue }
    if (c == "#") {                         # attribute opener: '#' [spaces] '['
      j = i + 1
      while (j <= n && substr(line, j, 1) ~ /[ \t\r]/) j++
      if (j <= n && substr(line, j, 1) == "[") { inattr = 1; adepth = 1; attrtxt = ""; i = j + 1; continue }
      loc = 0; i++; continue
    }
    if (isword(c)) {
      j = i
      while (j <= n && isword(substr(line, j, 1))) j++
      tok = substr(line, i, j - i)
      if (tok == "Local")       { loc = 1 }
      else if (tok == "Global") { loc = 0 }
      else if (tok == "Example" && loc) { printf "%s:%d: Local Example\n", FILENAME, FNR; bad = 1; loc = 0 }
      else                      { loc = 0 }
      i = j; continue
    }
    if (c != " " && c != "\t" && c != "\r") loc = 0   # any other punctuation flushes the chain (\r is line whitespace — CRLF/CR files)
    i++
  }
}
END { exit bad ? 1 : 0 }
