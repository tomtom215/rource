(* Test driver for Coq-extracted rource-math operations.
   Verifies that extracted code computes correct results. *)

open Rource_math_extracted

let () =
  (* Vec2 tests *)
  let v1 = zvec2_new 1 2 in
  let v2 = zvec2_new 3 4 in
  let sum = zvec2_add v1 v2 in
  assert (zvec2_x sum = 4);
  assert (zvec2_y sum = 6);
  assert (zvec2_dot v1 v2 = 11);
  assert (zvec2_cross v1 v2 = -2);
  assert (zvec2_length_squared (zvec2_new 3 4) = 25);
  Printf.printf "Vec2 tests passed\n";

  (* Vec3 tests *)
  let u1 = zvec3_new 1 2 3 in
  let u2 = zvec3_new 4 5 6 in
  let usum = zvec3_add u1 u2 in
  assert (zvec3_x usum = 5);
  assert (zvec3_y usum = 7);
  assert (zvec3_z usum = 9);
  assert (zvec3_dot u1 u2 = 32);
  let cross = zvec3_cross (zvec3_new 1 0 0) (zvec3_new 0 1 0) in
  assert (zvec3_x cross = 0);
  assert (zvec3_y cross = 0);
  assert (zvec3_z cross = 1);
  Printf.printf "Vec3 tests passed\n";

  (* Vec4 tests *)
  let w1 = zvec4_new 1 2 3 4 in
  let w2 = zvec4_new 5 6 7 8 in
  let wsum = zvec4_add w1 w2 in
  assert (zvec4_x wsum = 6);
  assert (zvec4_y wsum = 8);
  assert (zvec4_z wsum = 10);
  assert (zvec4_w wsum = 12);
  assert (zvec4_dot w1 w2 = 70);
  Printf.printf "Vec4 tests passed\n";

  (* Mat3 tests *)
  let m3i = zmat3_identity in
  let m3a = { zm3_0 = 1; zm3_1 = 2; zm3_2 = 3;
              zm3_3 = 4; zm3_4 = 5; zm3_5 = 6;
              zm3_6 = 7; zm3_7 = 8; zm3_8 = 9 } in
  let m3r = zmat3_mul m3i m3a in
  assert (zm3_0 m3r = 1);
  assert (zm3_4 m3r = 5);
  assert (zm3_8 m3r = 9);
  assert (zmat3_trace m3a = 15);
  let m3d = { zm3_0 = 1; zm3_1 = 0; zm3_2 = 0;
              zm3_3 = 0; zm3_4 = 2; zm3_5 = 0;
              zm3_6 = 0; zm3_7 = 0; zm3_8 = 3 } in
  assert (zmat3_determinant m3d = 6);
  Printf.printf "Mat3 tests passed\n";

  (* Mat4 tests *)
  let m4i = zmat4_identity in
  let m4a = { zm4_0 = 1; zm4_1 = 2; zm4_2 = 3; zm4_3 = 4;
              zm4_4 = 5; zm4_5 = 6; zm4_6 = 7; zm4_7 = 8;
              zm4_8 = 9; zm4_9 = 10; zm4_10 = 11; zm4_11 = 12;
              zm4_12 = 13; zm4_13 = 14; zm4_14 = 15; zm4_15 = 16 } in
  let m4r = zmat4_mul m4i m4a in
  assert (zm4_0 m4r = 1);
  assert (zm4_5 m4r = 6);
  assert (zm4_10 m4r = 11);
  assert (zm4_15 m4r = 16);
  assert (zmat4_trace m4a = 34);
  Printf.printf "Mat4 tests passed\n";

  Printf.printf "ALL EXTRACTION TESTS PASSED\n"
