# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# scan-agda-postulates.awk: list every postulate that one Agda source file
# declares, with the BUILTIN binding that gives it its meaning
# (standards/3-practice/PROOF-POLICY.adoc §8.4).
#
#   LC_ALL=C awk -v module=Agda.Primitive -f scripts/scan-agda-postulates.awk FILE
#
# Output: one line per postulated name, "module|name|binding", where binding
# is "BUILTIN <THING>" from a {-# BUILTIN <THING> <name> #-} pragma in FILE.
#
# The scan lexes as Agda does where a mistake could HIDE a postulate:
#   * nested block comments {- ... -} are blanked (newlines are kept);
#   * pragma bodies {-# ... #-} are blanked, and BUILTIN pragmas are read;
#   * a line comment starts at a run of two or more dashes that begins a token
#     and is followed by a space, a letter, a digit or the end of the line.
#     Any other dash run (for example an operator such as -->) stays code, so
#     a doubtful case can only find MORE postulates, never fewer.
# It refuses (exit 3) what it does not lex: a string literal, a character
# literal, a tab, a carriage return, a nested module, explicit layout braces
# after postulate, a declaration with no type signature, and a postulate with
# no BUILTIN binding.  A refusal is a
# gate failure: extend the scanner, never weaken it.
# Positive and negative controls: tests/trusted-base/ (run by
# scripts/check-trusted-base.sh on every gate run).

function refuse(msg) {
  printf "REFUSE %s (%s): %s\n", FILENAME, module, msg > "/dev/stderr"
  refused = 1
  exit 3
}

function idchar(c) {
  # A character that can continue an Agda name.  Any non-ASCII byte counts.
  return c !~ /^[ \n(){};.@"]$/ && c != ""
}

{ src = src $0 "\n" }

END {
  if (refused) exit 3
  if (module == "") { print "scan-agda-postulates.awk: set -v module=NAME" > "/dev/stderr"; exit 2 }
  if (index(src, "\t")) refuse("a tab character")
  if (index(src, "\r")) refuse("a carriage return (CRLF line ends are not lexed)")
  n = length(src); out = ""; i = 1; npragma = 0
  while (i <= n) {
    c = substr(src, i, 1); c2 = substr(src, i, 2); c3 = substr(src, i, 3)
    if (c3 == "{-#") {
      j = index(substr(src, i + 3), "#-}")
      if (j == 0) refuse("an unterminated pragma")
      body = substr(src, i + 3, j - 1)
      pragma[++npragma] = body
      blank = body; gsub(/[^\n]/, " ", blank)
      out = out "   " blank "   "
      i += 3 + j - 1 + 3
      continue
    }
    if (c2 == "{-") {
      depth = 1; k = i + 2
      while (k <= n && depth > 0) {
        d2 = substr(src, k, 2)
        if (d2 == "{-") { depth++; k += 2; continue }
        if (d2 == "-}") { depth--; k += 2; continue }
        k++
      }
      if (depth > 0) refuse("an unterminated block comment")
      blank = substr(src, i, k - i); gsub(/[^\n]/, " ", blank)
      out = out blank; i = k
      continue
    }
    if (c2 == "--") {
      prev = (i == 1) ? "\n" : substr(src, i - 1, 1)
      k = i; while (substr(src, k, 1) == "-") k++
      after = substr(src, k, 1)
      if (prev ~ /^[ \n(){};]$/ && (after == "\n" || after == " " || after ~ /^[A-Za-z0-9]$/ || k > n)) {
        while (k <= n && substr(src, k, 1) != "\n") k++
        blank = substr(src, i, k - i); gsub(/./, " ", blank)
        out = out blank; i = k
        continue
      }
    }
    if (c == "\"") refuse("a string literal (this scanner does not lex strings)")
    if (c == "'") {
      prev = (i == 1) ? "\n" : substr(src, i - 1, 1)
      if (!idchar(prev)) refuse("a character literal (this scanner does not lex them)")
    }
    out = out c; i++
  }

  # BUILTIN bindings: name -> "BUILTIN THING".
  for (p = 1; p <= npragma; p++) {
    body = pragma[p]; gsub(/\n/, " ", body)
    m = split(body, w, / +/); t = 0
    for (q = 1; q <= m; q++) if (w[q] != "") tok[++t] = w[q]
    if (t == 3 && tok[1] == "BUILTIN") binding[tok[3]] = "BUILTIN " tok[2]
    delete tok
  }

  nl = split(out, line, "\n")
  # One module per file: a BUILTIN binding is keyed by its short name, so a
  # nested module could reuse a bound name for an unbound postulate.  Refuse
  # any module declaration after the first, until the scan tracks scopes.
  nmod = 0
  for (l = 1; l <= nl; l++) if (line[l] ~ /(^|[ ;{])module( |$)/ && ++nmod > 1) refuse("a nested module on line " l)
  for (l = 1; l <= nl; l++) {
    s = line[l]
    if (!match(s, /(^|[ (){};])postulate([ (){};]|$)/)) continue
    pos = RSTART + (substr(s, RSTART, 1) == "p" ? 0 : 1)
    prefix = substr(s, 1, pos - 1)
    if (prefix ~ /[\200-\377]/) refuse("non-ASCII text before postulate on line " l)
    match(s, /^ */); indent = RLENGTH
    rest = substr(s, pos + 9)
    if (rest ~ /^ *\{/) refuse("explicit layout braces after postulate on line " l)
    ndecl = 0
    if (rest ~ /[^ ]/) {
      match(rest, /^ */); col = pos + 9 + RLENGTH - 1
      decl[++ndecl] = rest
      start = l + 1
    } else {
      col = -1; start = l + 1
    }
    for (k = start; k <= nl; k++) {
      t2 = line[k]
      if (t2 !~ /[^ ]/) continue
      match(t2, /^ */); ind = RLENGTH
      if (ind <= indent) break
      if (col < 0) col = ind
      if (ind < col) break
      if (ind == col) decl[++ndecl] = t2
      else decl[ndecl] = decl[ndecl] " " t2
    }
    l = k - 1
    if (ndecl == 0) refuse("an empty postulate block on line " l)
    for (d = 1; d <= ndecl; d++) {
      m = split(decl[d], w, / +/); colon = 0; nn = 0
      for (q = 1; q <= m; q++) {
        if (w[q] == "") continue
        if (w[q] == ":") { colon = 1; break }
        names[++nn] = w[q]
      }
      if (!colon || nn == 0) refuse("a postulate with no type signature: " decl[d])
      for (q = 1; q <= nn; q++) {
        if (!(names[q] in binding)) refuse("postulate " names[q] " has no BUILTIN binding")
        printf "%s|%s|%s\n", module, names[q], binding[names[q]]
      }
      delete names
    }
    delete decl
  }
}
