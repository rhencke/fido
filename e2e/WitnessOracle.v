(* Pinned-Go differential oracle: one rendered tree per one-source case, from the prelude program a chunk proves *)
From Fido Require Import WitnessRejectPrelude.

Declare ML Module "fido.emit".
Fido OracleExport (otransport dp_neg_string)  To "/workspace/diff/reject/neg_string".
Fido OracleExport (otransport dp_conv0)       To "/workspace/diff/reject/conv0".
Fido OracleExport (otransport dp_conv2)       To "/workspace/diff/reject/conv2".
Fido OracleExport (otransport dp_uint8_neg)   To "/workspace/diff/reject/uint8_neg".
Fido OracleExport (otransport dp_type_value)  To "/workspace/diff/reject/type_value".
Fido OracleExport (otransport dp_stmt_lit)    To "/workspace/diff/reject/stmt_lit".
Fido OracleExport (otransport dp_default_ovf) To "/workspace/diff/reject/default_ovf".
Fido OracleExport (otransport dp_no_main)     To "/workspace/diff/reject/no_main".
Fido OracleExport (otransport dp_multi_main)  To "/workspace/diff/reject/multi_main".
Fido OracleExport (otransport dp_short_dup)      To "/workspace/diff/reject/short_dup".
Fido OracleExport (otransport dp_short_count)    To "/workspace/diff/reject/short_count".
Fido OracleExport (otransport dp_short_nonew)    To "/workspace/diff/reject/short_nonew".
Fido OracleExport (otransport dp_short_allblank) To "/workspace/diff/reject/short_allblank".
Fido OracleExport (otransport dp_short_nonvar)   To "/workspace/diff/reject/short_nonvar".
Fido OracleExport (otransport dp_ok)          To "/workspace/diff/compiled/ok".
