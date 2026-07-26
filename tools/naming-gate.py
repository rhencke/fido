#!/usr/bin/env python3
"""A005 scoped-name policy gate.

The compiler is a total verifier for Rocq code: a missed rename simply fails to build.  Documentation has
no such verifier, so a stale name there is SILENT.  This gate is the only checker the prose will ever get,
and that is the reason it exists.

It REPORTS and never rewrites.  It is a policy gate, not a formatter.

What it fails on (Part I of the A005 migration directive):
  1. an old module or source-file name from Part B;
  2. an old public type/constructor name from Part C;
  3. a forbidden pseudo-namespace prefix in a DECLARATION position;
  4. a numbered theorem name (`thm<N>_`);
  5. a cryptic module alias (FM, FMF, PM, PMF, PMP, OFM, OFMF);
  6. a compatibility alias or re-export mapping an old name to a new one;
  7. a `Go[A-Z]` identifier in a live Rocq declaration, outside a small explicit allowlist;
  8. current documentation presenting an old name as live.

Rule 8 is deliberately narrow: history stays honest.  A live document MAY write
    `GoCompile` was renamed to `Compilable` by A005.
because the line carries an explicit historical marker.  It MAY NOT use `GoCompile` as the current
authority.  Lines carrying a marker are exempt; every other occurrence is a failure.

Run `python3 tools/naming-gate.py --self-test` for the negative controls: synthetic content that MUST be
flagged, and synthetic content that MUST NOT be.  A gate that cannot fail is not a gate.
"""
from __future__ import annotations
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Provenance, not current authority: these describe a world that had the old names.
EXCLUDED_TREES = (
    '.review/spec-closure-campaign/',   # the R1 spec-closure bundle is a historical artifact
    '.review/fcb/amendments/',          # amendments quote the names they retire
)
EXCLUDED_FILES = ('tools/naming-gate.py',)   # this file necessarily spells every old name

# ---------------------------------------------------------------- 1. old module / source-file names
OLD_MODULES = [
    'digits', 'Ints', 'Floats', 'Complexes', 'GoVersion', 'GoNames', 'GoAST', 'GoIndex', 'GoTypes',
    'GoCompile', 'GoSafe', 'GoRender', 'GoEmit',
]
OLD_FILES = ['axiom_gate', 'fido_sink', 'fido_apply', 'g_fido', 'Fido_sink']

# ---------------------------------------------------------------- 2. old public names
OLD_NAMES = [
    'FloatConst', 'ComplexConst', 'DecimalFloat',
    'DecimalComplex', 'TypedFloatConst', 'TypedComplexConst',
    'IdentifierSyntax', 'SupportedTypeName', 'TypeNameSyntax', 'TypeSyntax',
    'GoExpr', 'GoStmt', 'GoDecl', 'GoSourceFile', 'GoFileNode', 'GoFileMap', 'GoProgram',
    'SyntaxKind', 'NodeRole', 'NodeMeta', 'FileIndex', 'SyntaxView', 'SourceOccurrence',
    'IndexedProgram', 'NodeKey', 'NodeTable', 'GoType', 'GoConst', 'TypedConst', 'ConstInfo',
    'ResolvedConst', 'ExprUse', 'ResolveExpr', 'ProgramTyped', 'StmtTyped', 'DeclTyped', 'FileTyped',
    'SourceFileTyped', 'CompilableProgram', 'CompileFailure', 'CompileOutcome', 'LegacyCompileClass',
    'ExprFact', 'ExprOutcome', 'ExprWork', 'ExprWorkIndex', 'ExprWorkForest', 'ConversionWork',
    'OutcomeAccumulator', 'OutcomeTrace', 'ForestOutcomeTable', 'ExprFactTable', 'ForestExprFactTable',
    'AnnotatedExprWorkForest', 'ExpressionDiagnostics', 'ExpressionPhase', 'TypeNameFactTable',
    'ElaborationFacts', 'ElaborationCore', 'ElaborationDecision', 'ElaborationResult',
    'ProgramElaboration', 'CompilationInput', 'GoValue', 'SafeProgram', 'ValueDenotesConst',
    'DirectoryImage', 'RenderedConstInfoDenotes',
]
# A name retired from one module can be the CORRECT new name in another: `Typing.IntegerType` and
# `Safe.FloatValue` are right, while `Integer.IntegerType` and `Float.FloatValue` are the retired ones.
# Bare, they are indistinguishable without type information, so these are checked QUALIFIED only.
OLD_QUALIFIED = [
    'Integer.IntegerType', 'Float.FloatType', 'Complex.ComplexType',
    'Float.FloatValue', 'Complex.ComplexValue',
]

# Q-08's thirteen deleted surfaces must have zero live hits.
DELETED_SURFACES = [
    'program_elaboration_eta', 'result_ok_b', 'semantic_ok_flag', 'semantic_ok_flag_of_valid',
    'elaboration_ok_sig', 'elaboration_result_cases', 'elaborate_failed_ds',
    'cp_work', 'cp_trace', 'cp_layout', 'cp_plan', 'cp_diags', 'pe_result_on_core',
]

# ---------------------------------------------------------------- 3. forbidden declaration prefixes
FORBIDDEN_PREFIXES = [
    'ps_', 'ed_', 'ef_', 'tnf_', 'tnft_', 'ci_', 'ew_', 'ewi_', 'ewf_', 'cw_', 'cs_', 'oa_', 'fot_',
    'eft_', 'aewf_', 'feft_', 'ep_', 'ec_', 'pe_', 'cp_', 'cfail_', 'ppkg_', 'di_', 'sp_',
    'fp_', 'mp_', 'id_', 'tn_', 'stn_', 'fc_', 'dm_', 'fv_', 'tfc_', 'cc_', 'dc_', 'cv_', 'tcc_',
    'ts_', 'prog_', 'nm_', 'fi_', 'fr_', 'nr_', 'si_', 'ip_', 'nk_', 'wf_', 'pkg_', 'occ_', 'occs_',
    'fx_', 'ive_', 'rep_', 'scar_', 'anc_', 'reg_', 'rb_', 'rl_', 'rcd_', 'modpath_', 'goversion_',
    'gotype_', 'typed_const_', 'filemap_', 'packagemap_', 'go_compile',
]

# ---------------------------------------------------------------- 5. cryptic module aliases
CRYPTIC_ALIASES = ['FM', 'FMF', 'PM', 'PMF', 'PMP', 'OFM', 'OFMF', 'NM', 'NMF', 'Snap']

# ---------------------------------------------------------------- 7. Go-prefixed identifier allowlist
# Actual Go source/toolchain terms, not domain repetition.
GO_ALLOWLIST = {'Go1_23', 'GoModuleEntry'}   # the actual go.mod artifact

# A live doc line carrying one of these is describing history, which stays honest.
HISTORY_MARKERS = ('A005', 'renamed', 'was renamed', 'formerly', 'superseded', 'historical',
                   'before the migration', 'old name', 'pre-migration', 'retired')

DECL_KEYWORDS = (r'(?:Definition|Fixpoint|CoFixpoint|Inductive|Record|Theorem|Lemma|Corollary|Example'
                 r'|Instance|Class|Notation|Module)')
DECL_RE = re.compile(r'^\s*(?:Global\s+|Local\s+|#\[[^\]]*\]\s*)?' + DECL_KEYWORDS
                     + r'\s+([A-Za-z_][A-Za-z0-9_\']*)')
CTOR_RE = re.compile(r'^\s*\|\s*([A-Z][A-Za-z0-9_\']*)')
FIELD_RE = re.compile(r'[{;]\s*([a-z_][A-Za-z0-9_\']*)\s*:')


def strip_v_noise(text: str) -> str:
    """Blank out Rocq comments and string literals so prose is never read as code."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if depth == 0 and text.startswith('(*', i):
            depth = 1; out.append('  '); i += 2; continue
        if depth:
            if text.startswith('(*', i): depth += 1; out.append('  '); i += 2; continue
            if text.startswith('*)', i): depth -= 1; out.append('  '); i += 2; continue
            out.append('\n' if text[i] == '\n' else ' '); i += 1; continue
        if text[i] == '"':
            j = i + 1
            while j < n and not (text[j] == '"' and text[j - 1] != '\\'): j += 1
            out.append(' ' * (min(j, n - 1) - i + 1)); i = j + 1; continue
        out.append(text[i]); i += 1
    return ''.join(out)


def declaration_names(code: str):
    """(line_number, name) for every declaration, constructor and record field."""
    for idx, line in enumerate(code.splitlines(), 1):
        m = DECL_RE.match(line)
        if m:
            yield idx, m.group(1)
        m2 = CTOR_RE.match(line)
        if m2:
            yield idx, m2.group(1)
        # a single-line inductive carries its constructors on the declaration line itself
        if m and m.group(0).lstrip().startswith('Inductive') and ':=' in line:
            for c in re.findall(r'(?:\||:=)\s*([A-Z][A-Za-z0-9_\']*)', line.split(':=', 1)[1]):
                yield idx, c
            for c in re.findall(r'^[^|]*:=\s*([A-Z][A-Za-z0-9_\']*)', line):
                yield idx, c
        for f in FIELD_RE.findall(line):
            yield idx, f


def tracked_files():
    out = subprocess.run(['git', 'ls-files'], cwd=ROOT, capture_output=True, text=True).stdout.split()
    for f in out:
        if any(f.startswith(p) for p in EXCLUDED_TREES) or f in EXCLUDED_FILES:
            continue
        p = ROOT / f
        if p.is_file():
            yield f, p


def check_rocq(rel: str, text: str):
    """Rules 1-7 over a .v file, read as code (comments and strings blanked)."""
    bad = []
    code = strip_v_noise(text)
    for lineno, name in declaration_names(code):
        for pre in FORBIDDEN_PREFIXES:
            if name.startswith(pre):
                bad.append((rel, lineno, f'declaration `{name}` keeps the forbidden prefix `{pre}`'))
                break
        if re.match(r'^thm\d+_', name):
            bad.append((rel, lineno, f'numbered theorem name `{name}` — name the proposition'))
        if re.match(r'^[A-Z]{3,}[a-z]', name) and name not in GO_ALLOWLIST:
            bad.append((rel, lineno, f'constructor `{name}` leads with type initials'))
        if re.match(r'^Go[A-Z]', name) and name not in GO_ALLOWLIST:
            bad.append((rel, lineno, f'declaration `{name}` repeats the Go domain'))
    for idx, line in enumerate(code.splitlines(), 1):
        if re.match(r'\s*From\s+Stdlib\s+Require', line):
            continue                     # Rocq's own Floats/Ints are not our retired modules
        for old in OLD_MODULES + OLD_NAMES + OLD_FILES + DELETED_SURFACES:
            if re.search(r'(?<![\w.\'])' + re.escape(old) + r'(?![\w\'])', line):
                bad.append((rel, idx, f'old name `{old}` is still live here'))
        for oq in OLD_QUALIFIED:
            if oq in line:
                bad.append((rel, idx, f'retired qualified name `{oq}` is still live here'))
        m = re.match(r'\s*Module\s+(' + '|'.join(CRYPTIC_ALIASES) + r')\s*:?=', line)
        if m:
            bad.append((rel, idx, f'cryptic module alias `{m.group(1)}` — use the full name'))
        m2 = re.match(r'\s*(?:Definition|Notation)\s+([A-Za-z_][\w\']*)\s*:=\s*([A-Za-z_][\w\'.]*)\s*\.\s*$',
                      line)
        if m2 and m2.group(1) in OLD_NAMES:
            bad.append((rel, idx, f'compatibility alias `{m2.group(1)} := {m2.group(2)}` — '
                                  f'Git history is the only compatibility layer'))
    return bad


def check_prose(rel: str, text: str):
    """Rule 8 — a live document may describe an old name, but not present it as current."""
    bad = []
    for idx, line in enumerate(text.splitlines(), 1):
        if re.match(r'\s*From\s+Stdlib\s+Require', line):
            continue                     # Rocq's own Floats/Ints are not our retired modules
        if any(mark.lower() in line.lower() for mark in HISTORY_MARKERS):
            continue
        for old in OLD_MODULES + OLD_NAMES + OLD_FILES + DELETED_SURFACES:
            if old == 'digits':          # an ordinary English word in prose
                if re.search(r'(?<![\w.\'])digits\.v', line):
                    bad.append((rel, idx, 'old module `digits` presented as live'))
                continue
            if re.search(r'(?<![\w.\'/-])' + re.escape(old) + r'(?![\w\'])', line):
                bad.append((rel, idx, f'old name `{old}` presented as live'))
        for oq in OLD_QUALIFIED:
            if oq in line:
                bad.append((rel, idx, f'retired qualified name `{oq}` presented as live'))
    return bad


def run():
    violations = []
    for rel, path in tracked_files():
        try:
            text = path.read_text(encoding='utf-8')
        except (UnicodeDecodeError, OSError):
            continue
        if rel.endswith('.v'):
            violations += check_rocq(rel, text)
            # a comment is prose with no verifier -- the very thing this gate exists for
            violations += check_prose(rel, text)
        elif (rel.endswith(('.md', '.mlg', '.ml')) or rel.endswith('dune')
              or rel in ('Makefile', 'Dockerfile') or rel.startswith('tools/')):
            violations += check_prose(rel, text)
    return violations


# ------------------------------------------------------------------ negative controls
SELF_TESTS = [
    ('forbidden prefix in a declaration', check_rocq, 'Definition cp_program (x : nat) := x.\n', True),
    ('numbered theorem name',             check_rocq, 'Lemma thm7_enum_sound : True.\n', True),
    ('Go-domain repetition',              check_rocq, 'Record GoWidget := mk { a : nat }.\n', True),
    ('old module name in code',           check_rocq, 'Definition f := GoCompile.compile.\n', True),
    ('deleted Q-08 surface',              check_rocq, 'Definition g := pe_result_on_core.\n', True),
    ('cryptic module alias',              check_rocq, 'Module FM := Collections.FileMap.\n', True),
    ('compatibility alias',               check_rocq, 'Definition GoProgram := Syntax.Program.\n', True),
    ('old name presented as live',        check_prose, 'The `GoCompile` layer decides admissibility.\n', True),
    ('retired qualified name',           check_rocq, 'Definition f := Integer.IntegerType.\n', True),
    ('reused name under its new owner',  check_rocq, 'Definition f := Typing.IntegerType.\n', False),
    ('reused value name, new owner',     check_rocq, 'Definition v := Safe.FloatValue.\n', False),
    ('go-domain function family',        check_rocq, 'Lemma go_compile_untyped : True.\n', True),
    ('stdlib import is not our old name', check_rocq, 'From Stdlib Require Import Floats.SpecFloat.\n', False),
    ('constructor with type initials',   check_rocq, 'Inductive T := EOConvFail.\n', True),
    ('word-based constructor',           check_rocq, 'Inductive T := ConversionFailure.\n', False),
    ('stale name in a possessive',       check_prose, "the `CompilableProgram`'s retained layout\n", True),
    ('clean declaration',                 check_rocq, 'Definition compile (p : Syntax.Program) := p.\n', False),
    ('prefix inside a name, not leading', check_rocq, 'Definition scoped_cp_like := 0.\n', False),
    ('old name only in a comment',        check_rocq, '(* GoCompile was the old name *)\nDefinition c := 0.\n', False),
    ('old name only in a string',         check_rocq, 'Definition s := "GoCompile".\n', False),
    ('history line in prose',             check_prose, '`GoCompile` was renamed to `Compilable` by A005.\n', False),
    ('allowlisted Go term',               check_rocq, 'Inductive T := Go1_23.\n', False),
]


def self_test() -> int:
    failures = 0
    for label, checker, content, must_flag in SELF_TESTS:
        flagged = bool(checker('<self-test>', content))
        ok = (flagged == must_flag)
        if not ok:
            failures += 1
        verb = 'flags' if must_flag else 'accepts'
        print(f"  {'ok  ' if ok else 'FAIL'}  gate {verb}: {label}")
    if failures:
        print(f"fido: NAMING GATE SELF-TEST FAILED — {failures} control(s) wrong; the gate is not trustworthy")
        return 1
    print(f"fido: naming-gate self-test OK — {len(SELF_TESTS)} negative controls "
          f"({sum(1 for t in SELF_TESTS if t[3])} must-flag, "
          f"{sum(1 for t in SELF_TESTS if not t[3])} must-accept) ✓")
    return 0


def main() -> int:
    if '--self-test' in sys.argv:
        return self_test()
    if self_test():                      # the gate proves itself before it judges anything
        return 1
    violations = run()
    if violations:
        print(f"\nfido: NAMING GATE — {len(violations)} A005 violation(s):")
        for rel, line, msg in violations[:200]:
            print(f"  {rel}:{line}: {msg}")
        if len(violations) > 200:
            print(f"  ... and {len(violations) - 200} more")
        return 1
    print("fido: naming gate OK — no old module/type name, forbidden prefix, numbered theorem, cryptic "
          "alias, compatibility re-export, or stale documentation name survives ✓")
    return 0


if __name__ == '__main__':
    sys.exit(main())
