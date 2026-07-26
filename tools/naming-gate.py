#!/usr/bin/env python3
"""A005 / D-25 scoped-name policy gate.

The Rocq compiler is a total verifier for code: a missed rename simply fails to build.  Documentation and
source COMMENTS have no verifier at all, so a stale name there is silent.  This gate is the only checker
that surface will ever get.

It REPORTS and never rewrites.

Two exact input modes, because a gate enforced only on the ordinary working tree is not protection for the
proposed commit:

  working tree   python3 tools/naming-gate.py
                 requires a real Git worktree; enumerates with
                 `git ls-files --cached --others --exclude-standard`, checks the return code, includes
                 untracked non-ignored files, and FAILS if enumeration unexpectedly yields nothing.

  snapshot       python3 tools/naming-gate.py --root <dir> --snapshot
                 scans a complete exported tree with no .git present; fails if required roots or source
                 files are absent.  Never silently falls back to an empty set.

Enumeration that fails open is the defect this rebuild exists to remove: the previous gate ignored a
`git ls-files` failure and would scan zero files while reporting success.

Run `--self-test` for the negative controls.  A gate that cannot fail is not a gate; a gate that cannot
prove it fails is not evidence.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

# ───────────────────────────────────────────────────────────── exclusions
# Only these.  Active review documents, the live FCB, gates, fixtures, tools and source comments are all
# in scope: they are exactly where a stale name hides.
EXCLUDED_TREES = (
    '.review/spec-closure-campaign/',   # explicitly historical R1 bundle
    '.review/fcb/amendments/',          # an amendment must quote the names it retires
)
EXCLUDED_FILES = (
    'tools/naming-gate.py',                       # this file necessarily spells every retired name
    '.review/C4_IMPLEMENTATION_REPAIR_16.md',     # installed VERBATIM; markers cannot be added to it
)
BINARY_SUFFIXES = {'.png', '.jpg', '.jpeg', '.gif', '.zip', '.gz', '.pdf', '.vo', '.glob', '.hex'}

# ───────────────────────────────────────────────────────────── retired names
OLD_MODULES = ['digits', 'Ints', 'Floats', 'Complexes', 'GoVersion', 'GoNames', 'GoAST', 'GoIndex',
               'GoTypes', 'GoCompile', 'GoSafe', 'GoRender', 'GoEmit']
OLD_FILES = ['axiom_gate', 'fido_sink', 'fido_apply', 'g_fido', 'Fido_sink']

OLD_NAMES = [
    'FloatConst', 'ComplexConst', 'DecimalFloat', 'DecimalComplex', 'TypedFloatConst', 'TypedComplexConst',
    'IdentifierSyntax', 'SupportedTypeName', 'TypeNameSyntax', 'TypeSyntax',
    'GoExpr', 'GoStmt', 'GoDecl', 'GoSourceFile', 'GoFileNode', 'GoFileMap', 'GoProgram',
    'SyntaxKind', 'NodeRole', 'NodeMeta', 'FileIndex', 'SyntaxView', 'SourceOccurrence',
    'IndexedProgram', 'NodeKey', 'NodeTable', 'NodeKeyMap', 'NodeKeyMapFacts',
    'NodeKeyMapProps', 'NodeKeyMapOrd', 'NodeKey_OT', 'GoType', 'GoConst', 'TypedConst', 'ConstInfo',
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
# `Safe.FloatValue` are right; `Integer.IntegerType` and `Float.FloatValue` are the retired ones.
OLD_QUALIFIED = ['Integer.IntegerType', 'Float.FloatType', 'Complex.ComplexType',
                 'Float.FloatValue', 'Complex.ComplexValue']

# Lower-case concatenations of a removed scoped type.  Distinctive enough to match as substrings.
RETIRED_COMPOUNDS = ['goexpr', 'gostmt', 'godecl', 'gosourcefile', 'gosource', 'gocompile', 'gofilemap',
                     'gofilenode', 'goprogram', 'gotype', 'goconst', 'govalue',
                     'nodekeymap', 'nodekey', 'typesyntax', 'supportedtypename',
                     'decimalfloat', 'decimalcomplex', 'programtyped', 'compilableprogram']

# Q-08's thirteen deleted surfaces must have zero live hits.
DELETED_SURFACES = ['program_elaboration_eta', 'result_ok_b', 'semantic_ok_flag',
                    'semantic_ok_flag_of_valid', 'elaboration_ok_sig', 'elaboration_result_cases',
                    'elaborate_failed_ds', 'cp_work', 'cp_trace', 'cp_layout', 'cp_plan', 'cp_diags',
                    'pe_result_on_core',
                    # repair 15 §9/§12 — the stripped result peer and the reconstruction bridges
                    'ElaborationOK', 'ElaborationFailed', 'elaborate_indexed', 'elaborate_phase_raw_eq',
                    'elaborate_diags_eq_elaboration', 'elaborate_failed_not_valid',
                    'over_program_failure_carries_core_diags',
                    # repair 15 §7 — the second capability-mint path
                    'elaboration_ok_core', 'compilable_of_valid',
                    # repair 15 §8 — surfaces that named a now-sealed constructor and could not survive it
                    'compile_on_core', 'compile_projects_elaborate', 'failure_diagnostics_make',
                    # repair 14's deletions, which never entered this table — which is exactly how
                    # ARCHITECTURE.md went on citing `cp_prov` as current for a whole repair cycle
                    'cp_prov', 'compilable_prov', 'elaboration_ok_full', 'elaborate_ok_whole',
                    'elaborate_failed_whole', 'elaborate_ok_seals_facts', 'elaborate_ok_seals_tnfacts']

# Pseudo-qualifier SEGMENTS.  Checked anywhere in an identifier, not merely at position zero: an embedded
# `cp` is exactly as much a fake namespace as a leading one.
PSEUDO_SEGMENTS = {
    'ps', 'ed', 'ef', 'tnf', 'tnft', 'ci', 'ew', 'ewi', 'ewf', 'cw', 'cs', 'oa', 'fot', 'eft', 'aewf',
    'feft', 'ep', 'ec', 'pe', 'cp', 'cfail', 'ppkg', 'di', 'sp', 'fp', 'mp', 'stn', 'fc', 'dm', 'fv',
    'tfc', 'cc', 'dc', 'cv', 'tcc', 'ts', 'nm', 'fi', 'fr', 'nr', 'si', 'ip', 'nk', 'scar', 'ive',
    'rb', 'rl', 'rcd', 'ss', 'pm', 'pmf', 'pmp', 'fm', 'fmf', 'ofm', 'ofmf',
}
# Segments that look like a pseudo-qualifier but are real words or real Go/维 tokens in this domain.
SEGMENT_ALLOWLIST = {'go'}

CRYPTIC_ALIASES = ['FM', 'FMF', 'PM', 'PMF', 'PMP', 'OFM', 'OFMF', 'NM', 'NMF', 'Snap']
GO_ALLOWLIST = {'Go1_23', 'GoModuleEntry'}      # real Go artefacts, not domain repetition

HISTORY_MARKERS = ('a005', 'renamed', 'formerly', 'superseded', 'historical', 'before the migration',
                   'old name', 'pre-migration', 'retired', 'was the', 'no longer')

# ───────────────────────────────────────────────────────────── declaration kinds
UPPER_KINDS = {'Inductive', 'Record', 'Class', 'Module', 'Variant', 'constructor'}
SNAKE_KINDS = {'Theorem', 'Lemma', 'Corollary', 'Example', 'Instance'}
DECL_KEYWORDS = (r'Definition|Fixpoint|CoFixpoint|Inductive|Variant|Record|Theorem|Lemma|Corollary'
                 r'|Example|Instance|Class|Module\s+Type|Module|Notation')
DECL_RE = re.compile(r'^\s*(?:Global\s+|Local\s+|Program\s+|#\[[^\]]*\]\s*)*'
                     r'(' + DECL_KEYWORDS + r')\s+("?[A-Za-z_][A-Za-z0-9_\']*"?)')


def strip_code_noise(text: str) -> str:
    """Blank Rocq comments and string literals, preserving line structure, so prose is never read as code."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if depth == 0 and text.startswith('(*', i):
            depth, i = 1, i + 2; out.append('  '); continue
        if depth:
            if text.startswith('(*', i): depth += 1; i += 2; out.append('  '); continue
            if text.startswith('*)', i): depth -= 1; i += 2; out.append('  '); continue
            out.append('\n' if text[i] == '\n' else ' '); i += 1; continue
        if text[i] == '"':
            j = i + 1
            while j < n and not (text[j] == '"' and text[j - 1] != '\\'):
                out.append('\n' if text[j] == '\n' else ' '); j += 1
            out.append('  '); i = j + 1; continue
        out.append(text[i]); i += 1
    return ''.join(out)


def statements(code: str):
    """Yield (start_line, text) for each Rocq statement — a '.' followed by whitespace ends one.
    Statement-aware so multiline records, inductives and constructors are parsed whole."""
    line, buf, start = 1, [], 1
    i, n = 0, len(code)
    while i < n:
        ch = code[i]
        buf.append(ch)
        if ch == '\n':
            line += 1
        if ch == '.' and (i + 1 >= n or code[i + 1] in ' \t\r\n'):
            text = ''.join(buf).strip()
            if text:
                yield start, text
            buf, start = [], line
        i += 1
    if ''.join(buf).strip():
        yield start, ''.join(buf).strip()


def declared(code: str):
    """(line, kind, name) for declarations, constructors and record fields — multiline aware."""
    for line, stmt in statements(code):
        m = DECL_RE.match(stmt)
        if not m:
            continue
        kind = 'Module' if m.group(1).startswith('Module') else m.group(1)
        name = m.group(2).strip('"')
        yield line, kind, name
        # Constructors are parsed as GENERAL Rocq identifiers and judged afterwards.  Matching only
        # `[A-Z]...` here was the false-green: a lower-case constructor was never extracted, so no rule
        # could reject it — the gate could not see the declarations it existed to catch.
        if kind in ('Inductive', 'Variant'):
            body = stmt.split(':=', 1)[1] if ':=' in stmt else ''
            # split on the bar and take the LEADING identifier of each alternative.  The old form required a
            # `|` or `:=` immediately before the name, which silently skipped the FIRST constructor of every
            # `Inductive T := First | ...` — a second blind spot on top of the case one.
            for piece in body.split('|'):
                m = re.match(r"\s*([A-Za-z_][A-Za-z0-9_']*)", piece)
                if m:
                    yield line, 'constructor', m.group(1)
        if kind == 'Record':
            body = stmt.split(':=', 1)[1] if ':=' in stmt else ''
            ctor = re.match(r'\s*([A-Za-z_][A-Za-z0-9_\']*)\s*\{', body)
            if ctor:
                yield line, 'constructor', ctor.group(1)
            for f in re.findall(r"[{;]\s*([a-z_][A-Za-z0-9_']*)\s*:", body):
                yield line, 'field', f


def segments(name: str):
    """Identifier split into semantic segments across underscores AND camelCase boundaries."""
    parts = []
    for chunk in name.split('_'):
        parts += [s for s in re.split(r'(?<=[a-z0-9])(?=[A-Z])', chunk) if s]
    return [p.lower() for p in parts]


# ───────────────────────────────────────────────────────────── checks
def check_code(rel: str, text: str):
    bad = []
    code = strip_code_noise(text)
    for line, kind, name in declared(code):
        low = name.lower()
        for compound in RETIRED_COMPOUNDS:
            if compound in low:
                bad.append((rel, line, f'{kind} `{name}` contains the retired compound `{compound}`'))
                break
        for seg in segments(name):
            if seg in PSEUDO_SEGMENTS and seg not in SEGMENT_ALLOWLIST:
                bad.append((rel, line, f'{kind} `{name}` uses `{seg}` as a pseudo-qualifier segment'))
                break
        if re.search(r'(?:^|_)thm\d+', low):
            bad.append((rel, line, f'{kind} `{name}` is a numbered theorem — name the proposition'))
        if re.search(r'fixture_\d', low):
            bad.append((rel, line, f'{kind} `{name}` is a numbered fixture — name the scenario'))
        if name.endswith('_T') or name.endswith('_t') or name.endswith('_impl'):
            bad.append((rel, line, f'{kind} `{name}` uses a cryptic representation suffix'))
        if re.match(r'^Go[A-Z]', name) and name not in GO_ALLOWLIST:
            bad.append((rel, line, f'{kind} `{name}` repeats the Go domain'))
        if re.match(r'^[A-Z]{3,}[a-z]', name) and name not in GO_ALLOWLIST:
            bad.append((rel, line, f'{kind} `{name}` leads with type initials'))
        # §3.1 rule 4: universal mathematical / actual-source tokens may keep their case
        residue = re.sub(r'(?:^|_)(Z|N|F32|F64|C64|C128|ASCII|EOF)(?=_|$)', '_', name)
        if kind in SNAKE_KINDS and re.search(r'[A-Z]', residue):
            bad.append((rel, line, f'{kind} `{name}` must be lower_snake_case'))
        if kind in UPPER_KINDS and not re.match(r'^[A-Z]', name):
            bad.append((rel, line, f'{kind} `{name}` must be UpperCamelCase'))
        if kind == 'field' and re.search(r'[A-Z]', name):
            bad.append((rel, line, f'record field `{name}` must be lower_snake_case'))
    for idx, line in enumerate(code.splitlines(), 1):
        if re.match(r'\s*From\s+Stdlib\s+Require', line):
            continue                       # Rocq's own Floats/Ints are not our retired modules
        for old in OLD_MODULES + OLD_NAMES + OLD_FILES + DELETED_SURFACES:
            if re.search(r"(?<![\w.'])" + re.escape(old) + r"(?![\w'])", line):
                bad.append((rel, idx, f'retired name `{old}` is still live here'))
        for oq in OLD_QUALIFIED:
            if oq in line:
                bad.append((rel, idx, f'retired qualified name `{oq}` is still live here'))
        m = re.match(r'\s*Module\s+(' + '|'.join(CRYPTIC_ALIASES) + r')\s*:?=', line)
        if m:
            bad.append((rel, idx, f'cryptic module alias `{m.group(1)}`'))
    return bad


HISTORICAL_DOC = re.compile(r'^\s*(?:<!--\s*)?HISTORICAL DOCUMENT\b', re.M)


def check_prose(rel: str, text: str):
    """A live document may describe a retired name; it may not present one as current.

    A document may declare ITSELF historical with a `HISTORICAL DOCUMENT` line in its first 20 lines —
    visible to a reader, auditable in the diff, and never a silent entry in an exclusion list."""
    bad = []
    if HISTORICAL_DOC.search('\n'.join(text.splitlines()[:20])):
        return bad
    for idx, line in enumerate(text.splitlines(), 1):
        if re.match(r'\s*From\s+Stdlib\s+Require', line):
            continue
        if any(mark in line.lower() for mark in HISTORY_MARKERS):
            continue
        for old in OLD_MODULES + OLD_NAMES + OLD_FILES + DELETED_SURFACES:
            if old == 'digits':
                if re.search(r"(?<![\w.'])digits\.v", line):
                    bad.append((rel, idx, 'retired module `digits` presented as live'))
                continue
            if re.search(r"(?<![\w.'/-])" + re.escape(old) + r"(?![\w'])", line):
                bad.append((rel, idx, f'retired name `{old}` presented as live'))
        for oq in OLD_QUALIFIED:
            if oq in line:
                bad.append((rel, idx, f'retired qualified name `{oq}` presented as live'))
        for compound in RETIRED_COMPOUNDS:
            if re.search(r"(?<![\w.'])" + compound + r"(?=[_\W]|$)", line):
                bad.append((rel, idx, f'retired compound `{compound}` presented as live'))
                break
    return bad


# ───────────────────────────────────────────────────────────── enumeration
class EnumerationError(RuntimeError):
    pass


def enumerate_worktree(root: Path):
    if not (root / '.git').exists():
        raise EnumerationError(f'{root} is not a Git worktree — working-tree mode needs one '
                               f'(use --root <dir> --snapshot for an exported tree)')
    proc = subprocess.run(['git', 'ls-files', '--cached', '--others', '--exclude-standard'],
                          cwd=root, capture_output=True, text=True)
    if proc.returncode != 0:
        raise EnumerationError(f'git ls-files failed (rc={proc.returncode}): {proc.stderr.strip()}')
    rels = [f for f in proc.stdout.split('\n') if f]
    if not rels:
        raise EnumerationError('git ls-files returned no files — refusing to report success on nothing')
    return rels


def enumerate_snapshot(root: Path):
    if not root.is_dir():
        raise EnumerationError(f'snapshot root {root} does not exist')
    rels = [str(p.relative_to(root)) for p in root.rglob('*')
            if p.is_file() and '.git' not in p.parts]
    if not rels:
        raise EnumerationError(f'snapshot root {root} is empty — refusing to report success on nothing')
    required = ['Compilable.v', 'Syntax.v', 'Index.v', 'Typing.v', 'Safe.v', 'Render.v', 'Emit.v',
                'dune', 'Makefile']
    missing = [r for r in required if not (root / r).exists()]
    if missing:
        raise EnumerationError(f'snapshot root {root} is incomplete — missing {", ".join(missing)}')
    return rels


def selected(root: Path, rels):
    for rel in sorted(rels):
        if any(rel.startswith(p) for p in EXCLUDED_TREES) or rel in EXCLUDED_FILES:
            continue
        p = root / rel
        if not p.is_file() or p.suffix.lower() in BINARY_SUFFIXES:
            continue
        yield rel, p


def rocq_scope(root: Path):
    """Every Rocq source the gate MUST have parsed: the certified modules dune declares, plus the gate and
    e2e sources.  A file silently skipped — unreadable, mis-enumerated, excluded by accident — would make
    'no violation' mean 'nothing looked at', which is the failure mode this whole rebuild exists to remove."""
    expected = set()
    dune = root / 'dune'
    if dune.is_file():
        m = re.search(r'\(modules\s+([^)]*)\)', dune.read_text(encoding='utf-8'))
        if m:
            expected |= {f'{mod}.v' for mod in m.group(1).split()}
    for sub in ('gate', 'e2e'):
        d = root / sub
        if d.is_dir():
            expected |= {f'{sub}/{f.name}' for f in d.iterdir() if f.suffix == '.v'}
    return expected


def run(root: Path, snapshot: bool):
    rels = enumerate_snapshot(root) if snapshot else enumerate_worktree(root)
    violations, examined, parsed = [], 0, set()
    for rel, path in selected(root, rels):
        try:
            text = path.read_text(encoding='utf-8')
        except (UnicodeDecodeError, OSError):
            continue                       # genuinely binary; not a text surface
        examined += 1
        if rel.endswith('.v'):
            violations += check_code(rel, text)
            parsed.add(rel)
        violations += check_prose(rel, text)   # comments are prose with no verifier
    missed = sorted(rocq_scope(root) - parsed)
    if missed:
        raise EnumerationError(
            'the gate did not parse every Rocq source in its stated scope — missing: '
            + ', '.join(missed))
    return violations, examined


# ───────────────────────────────────────────────────────────── negative controls
SELF_TESTS = [
    ('leading forbidden prefix',          check_code, 'Definition cp_program (x : nat) := x.\n', True),
    ('embedded pseudo-qualifier segment', check_code, 'Definition scoped_cp_like := 0.\n', True),
    ('retired compound goexpr',           check_code, 'Lemma goexpr_eq_dec : True.\n', True),
    ('retired compound nodekey',          check_code, 'Lemma nodekey_eqb : True.\n', True),
    ('retired type in a theorem name',    check_code, 'Theorem elaborate_ok_iff_GoCompile : True.\n', True),
    ('numbered fixture',                  check_code, 'Example fixture_2001_plan : True.\n', True),
    ('numbered theorem',                  check_code, 'Lemma thm7_enum_sound : True.\n', True),
    ('uppercase theorem family',          check_code, 'Lemma StronglySorted_map : True.\n', True),
    ('cryptic _T representation',         check_code, 'Record FileRef_T := mk { a : nat }.\n', True),
    ('multiline record field',            check_code,
     'Record R := mk {\n  cp_program : nat ;\n  other : nat\n}.\n', True),
    ('multiline inductive constructor',   check_code,
     'Inductive T :=\n| EOConvFail : T\n| Other : T.\n', True),
    ('lower-case inductive',              check_code, 'Inductive thing := A.\n', True),
    # the false-green the reviewer found: these were ACCEPTED because the parser never saw them
    ('lower-case record constructor',     check_code, 'Record GoodType := make_bad { value : nat }.\n', True),
    ('lower-case inductive constructor',  check_code, 'Inductive GoodType := make_bad : GoodType.\n', True),
    ('lower-case ctor, multiline record', check_code,
     'Record GoodType := make_bad {\n  value : nat\n}.\n', True),
    ('lower-case ctor among good ones',   check_code, 'Inductive T := Good | make_bad | AlsoGood.\n', True),
    ('lower-case variant constructor',    check_code, 'Variant V := make_bad.\n', True),
    ('Go-domain repetition',              check_code, 'Record GoWidget := mk { a : nat }.\n', True),
    ('deleted Q-08 surface',              check_code, 'Definition g := pe_result_on_core.\n', True),
    ('retired qualified name',            check_code, 'Definition f := Integer.IntegerType.\n', True),
    ('old live prose name',               check_prose, 'The `GoCompile` layer decides admissibility.\n', True),
    ('retired compound in prose',         check_prose, 'See `nodekey_eqb` for the ordering.\n', True),
    # must NOT flag
    ('clean declaration',                 check_code, 'Definition compile (p : nat) := p.\n', False),
    ('clean proof name',                  check_code, 'Lemma strongly_sorted_map : True.\n', False),
    ('UpperCamelCase type Definition',    check_code, 'Definition Syntax := nat.\n', False),
    ('retired name only in a comment',    check_code, '(* GoCompile was the old name *)\nDefinition c := 0.\n', False),
    ('retired name only in a string',     check_code, 'Definition s := "GoCompile".\n', False),
    ('reused name under its new owner',   check_code, 'Definition f := Typing.IntegerType.\n', False),
    ('historical sentence in prose',      check_prose, '`GoCompile` was renamed to `Compilable` by A005.\n', False),
    ('legitimate semantic compound',      check_code, 'Lemma package_clause_eq_dec : True.\n', False),
    ('actual Go token',                   check_code, 'Inductive T := Go1_23.\n', False),
    ('Go artefact allowlisted',           check_code, 'Inductive T := GoModuleEntry.\n', False),
    # …and the must-ACCEPT twins, so the new rule cannot pass by rejecting everything
    ('UpperCamelCase record ctor',        check_code, 'Record GoodType := MakeGood { value : nat }.\n', False),
    ('UpperCamelCase inductive ctor',     check_code, 'Inductive GoodType := MakeGood : GoodType.\n', False),
    ('several UpperCamelCase ctors',      check_code, 'Inductive T := First | Second | Third.\n', False),
    ('anonymous record constructor',      check_code, 'Record GoodType := { value : nat }.\n', False),
]


def self_test() -> int:
    failures = 0
    for label, checker, content, must_flag in SELF_TESTS:
        flagged = bool(checker('<self-test>', content))
        if flagged != must_flag:
            failures += 1
            print(f"  FAIL  gate {'flags' if must_flag else 'accepts'}: {label}")
    # enumeration controls — the defect this rebuild removes
    try:
        enumerate_worktree(Path('/'))
        print('  FAIL  working-tree mode outside Git must raise'); failures += 1
    except EnumerationError:
        pass
    try:
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            enumerate_snapshot(Path(d))
            print('  FAIL  snapshot mode on an empty export must raise'); failures += 1
    except EnumerationError:
        pass
    try:
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / 'Compilable.v').write_text('x')
            enumerate_snapshot(Path(d))
            print('  FAIL  snapshot mode on an incomplete export must raise'); failures += 1
    except EnumerationError:
        pass
    n = len(SELF_TESTS) + 3
    if failures:
        print(f"fido: NAMING GATE SELF-TEST FAILED — {failures} of {n} controls wrong; "
              f"the gate is not trustworthy")
        return 1
    print(f"fido: naming-gate self-test OK — {n} negative controls "
          f"({sum(1 for t in SELF_TESTS if t[3])} must-flag, "
          f"{sum(1 for t in SELF_TESTS if not t[3])} must-accept, 3 enumeration fail-closed) ✓")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description='A005 scoped-name policy gate (reports, never rewrites)')
    ap.add_argument('--root', default=None, help='tree to scan (default: the repository root)')
    ap.add_argument('--snapshot', action='store_true', help='scan an exported tree with no .git')
    ap.add_argument('--self-test', action='store_true', help='run the negative controls only')
    args = ap.parse_args()

    root = Path(args.root).resolve() if args.root else Path(__file__).resolve().parent.parent
    if args.self_test:
        return self_test()
    if self_test():                    # the gate proves itself before it judges anything
        return 1
    try:
        violations, examined = run(root, args.snapshot)
    except EnumerationError as e:
        print(f"fido: NAMING GATE — enumeration failed, refusing to pass: {e}")
        return 1
    mode = 'snapshot' if args.snapshot else 'working tree'
    if violations:
        print(f"\nfido: NAMING GATE ({mode}, root {root}, {examined} files) — "
              f"{len(violations)} A005 violation(s):")
        for rel, line, msg in violations[:200]:
            print(f"  {rel}:{line}: {msg}")
        if len(violations) > 200:
            print(f"  ... and {len(violations) - 200} more")
        return 1
    print(f"fido: naming gate OK — mode {mode}, root {root}, {examined} files examined; no retired module, "
          f"type, compound or deleted surface; no pseudo-qualifier segment, numbered theorem or fixture, "
          f"cryptic representation suffix, or declaration-kind casing violation; no stale name presented as "
          f"live in documentation or comments ✓")
    return 0


if __name__ == '__main__':
    sys.exit(main())
