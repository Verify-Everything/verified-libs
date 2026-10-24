import Crc32fast.Extracted.Funs
import Crc32fast.SpecLemmas

open Aeneas Aeneas.Std crc32fast Crc32Spec

/-- The spec-level slice-by-16 table, as a list of rows. -/
def tblRows : List (List (BitVec 32)) :=
  (List.range 16).map (fun k => (List.range 256).map (fun n => tbl k (BitVec.ofNat 8 n)))

set_option maxRecDepth 100000 in
/-- Every one of the 4096 constants in `CRC32_TABLE` is what the spec says it is. -/
theorem table_eq : table.CRC32_TABLE.val.map (fun row => row.val.map (·.bv)) = tblRows := by
  unfold table.CRC32_TABLE
  decide +kernel
