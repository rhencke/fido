# Token-aware Local-Example detector — the ENGINE of smart-ctor-gate.sh check 6 (see there for WHY).
# A tiny Rocq lexer, char-by-char with cross-line state per file: tracks NESTED (* *) comments,
# "…" string literals (multi-line, backslash escapes), and #[…] attributes (multi-line,
# bracket-nested).  It reports FILE:LINE for every `Example` token whose immediately preceding
# TOKEN — with any amount of whitespace, newlines, and comments between — is the locality marker:
# the `Local` vernacular or a #[…] attribute containing the word `local`.
# DETECTION BOUNDARY (exact): locality marker DIRECTLY followed by `Example`; any other token
# between them breaks adjacency and is not claimed.  Comment/string occurrences are excluded by
# the lexer states.  Exits 1 iff any hit (hits printed on stdout).
function isword(c) { return c ~ /[A-Za-z0-9_']/ }
FNR == 1 { cdepth = 0; instr = 0; inattr = 0; adepth = 0; attrtxt = ""; prevtok = "" }
{
  line = $0; n = length(line); i = 1
  while (i <= n) {
    c = substr(line, i, 1); c2 = substr(line, i, 2)
    if (cdepth > 0) {
      if (c2 == "(*") { cdepth++; i += 2; continue }
      if (c2 == "*)") { cdepth--; i += 2; continue }
      i++; continue
    }
    if (instr) {
      if (c == "\\") { i += 2; continue }
      if (c == "\"") instr = 0
      i++; continue
    }
    if (inattr) {
      if (c == "[") adepth++
      if (c == "]") {
        adepth--
        if (adepth == 0) {
          inattr = 0
          if (attrtxt ~ /(^|[^A-Za-z0-9_])local([^A-Za-z0-9_]|$)/) prevtok = "#[local]"
          else prevtok = "#[attr]"
        }
      } else attrtxt = attrtxt c
      i++; continue
    }
    if (c2 == "(*") { cdepth++; i += 2; continue }
    if (c == "\"") { instr = 1; i++; continue }
    if (c == "#") {
      j = i + 1
      while (j <= n && substr(line, j, 1) ~ /[ \t]/) j++
      if (j <= n && substr(line, j, 1) == "[") { inattr = 1; adepth = 1; attrtxt = ""; i = j + 1; continue }
      prevtok = ""; i++; continue
    }
    if (isword(c)) {
      j = i
      while (j <= n && isword(substr(line, j, 1))) j++
      tok = substr(line, i, j - i)
      if (tok == "Example" && (prevtok == "Local" || prevtok == "#[local]")) {
        printf "%s:%d: %s Example\n", FILENAME, FNR, prevtok
        bad = 1
      }
      prevtok = tok
      i = j; continue
    }
    if (c != " " && c != "\t") prevtok = ""
    i++
  }
}
END { exit bad ? 1 : 0 }
