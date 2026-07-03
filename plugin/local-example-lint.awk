# Rocq-lexical Local-Example detector (engine of smart-ctor-gate.sh check 6).  Char-level scanner
# with cross-line state: nested (* *) comments; strings with Rocq's doubled-"" escape (backslash
# literal); multi-line #[ ... ] attribute blocks whose embedded strings/comments are inert.
# LOCALITY ACCUMULATES: `Local` or a #[...local...] attribute decorates the next command token
# (non-local attributes preserve it; `Global`/any ordinary token clears it); a decorated
# `Example` is a hit.  Exits 1 iff any hit.
function isword(c) { return c ~ /[A-Za-z0-9_']/ }
FNR == 1 { cdepth = 0; instr = 0; inattr = 0; inastr = 0; adepth = 0; attrtxt = ""; loc = 0 }
{
  line = $0; n = length(line); i = 1
  while (i <= n) {
    c = substr(line, i, 1); c2 = substr(line, i, 2)
    if (cdepth > 0) {
      if (c2 == "(*") { cdepth++; i += 2; continue }
      if (c2 == "*)") { cdepth--; i += 2; continue }
      i++; continue
    }
    if (inastr) {
      if (c == "\"") { if (c2 == "\"\"") { i += 2; continue } inastr = 0 }
      i++; continue
    }
    if (instr) {
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
        } else attrtxt = attrtxt c
        i++; continue
      }
      attrtxt = attrtxt c; i++; continue
    }
    if (c2 == "(*") { cdepth++; i += 2; continue }
    if (c == "\"") { instr = 1; i++; continue }
    if (c == "#") {
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
    if (c != " " && c != "\t" && c != "\r") loc = 0   # punctuation flushes the chain
    i++
  }
}
END { exit bad ? 1 : 0 }
