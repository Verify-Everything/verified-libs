import Proofs
import Proofs.Sets
import Proofs.Traits
import Proofs.Alloc
open percent_encoding.Proofs percent_encoding.Spec
-- Encoder / decoder core
#print axioms percent_encode_byte_spec
#print axioms next_chunk_spec
#print axioms encode_next_spec
#print axioms percent_encode_correct
#print axioms after_percent_sign_spec
#print axioms decode_next_spec
#print axioms percent_decode_correct
#print axioms percent_encode_output_allowed
#print axioms percent_roundtrip
#print axioms decode_encode
-- AsciiSet
#print axioms contains_spec
#print axioms should_percent_encode_spec
#print axioms add_spec
#print axioms remove_spec
#print axioms union_spec
#print axioms add_op_spec
#print axioms complement_spec
#print axioms not_op_spec
#print axioms EMPTY_spec
#print axioms add_nonascii_panics
#print axioms remove_nonascii_panics
#print axioms CONTROLS_spec
#print axioms NON_ALPHANUMERIC_spec
#print axioms roundtrip_NON_ALPHANUMERIC
#print axioms CONTROLS_no_roundtrip
#print axioms BITS_PER_CHUNK_spec
-- Derived traits and wrappers
#print axioms asciiSet_eq_spec
#print axioms asciiSet_eq_iff_inSet
#print axioms percentEncode_eq_spec
#print axioms asciiSet_assert_fields_are_eq
#print axioms percentEncode_assert_fields_are_eq
#print axioms percentEncode_clone_spec
#print axioms percentDecode_clone_spec
#print axioms utf8_percent_encode_correct
#print axioms percent_decode_str_correct
#print axioms asciiSet_debug_ok
#print axioms percentEncode_debug_ok
-- size_hint
#print axioms encode_size_hint_spec
#print axioms decode_size_hint_spec
-- alloc feature and Display
#print axioms cow_from_encode_spec
#print axioms position_of_percent_spec
#print axioms decode_from_percent_spec
#print axioms decode_if_any_spec
#print axioms if_any_spec
#print axioms cow_from_decode_spec
#print axioms decode_utf8_spec
#print axioms decode_utf8_lossy_spec
#print axioms write_chunks_spec
#print axioms write_chunks_buffer
#print axioms display_fmt_spec
#print axioms free_decode_utf8_lossy_spec
#print axioms static_assert_spec
