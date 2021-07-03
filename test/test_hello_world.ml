open! Base

let run_type_test s =
  s
  |> Parsexp.Single.parse_string_exn
  |> [%of_sexp: Hello_world.Term.t]
  |> Hello_world.type_term ~ctx:Hello_world.Ctx.empty
  |> Hello_world.Type.coalesce_type
  |> [%sexp_of: Hello_world.Type.t]
  |> Sexp.to_string_hum
  |> Stdio.print_endline
;;

let%expect_test _ = 
  run_type_test {| (int_lit 5) |};
[%expect {| (PrimitiveType int) |}]

let%expect_test _ = 
  run_type_test {| (lam (name a) (body (var a))) |};
[%expect {| (FunctionType (param (Type_variable 0)) (body (Type_variable 0))) |}]

let%expect_test _ = 
  run_type_test {| (rcd (fields ((a (int_lit 5)) (b (int_lit 10))))) |};
[%expect {| (RecordType (fields ((a (PrimitiveType int)) (b (PrimitiveType int))))) |}]

let%expect_test _ = 
  run_type_test {| (rcd (fields ((a (lam (name a) (body (var a)))) (b (int_lit 10))))) |};
[%expect {|
  (RecordType
   (fields
    ((a (FunctionType (param (Type_variable 1)) (body (Type_variable 1))))
     (b (PrimitiveType int))))) |}]

let%expect_test _ = 
  run_type_test {| (lam (name a) (body (app (lhs (sel (rcv (var a)) (field a))) (rhs (sel (rcv (var a)) (field b)))))) |};
  (* 'b ^ { a : 'e ^ ('d -> 'c) } ^ { b : 'd} -> 'c *)
  (* { a : ('d -> 'c) } ^ { b : 'd } -> 'c *)
  (* { a : ('d -> 'c);  b : 'd } -> 'c *)
[%expect {|
  (FunctionType
   (param
    (Inter
     (lhs
      (Inter (lhs (Type_variable 2))
       (rhs
        (RecordType
         (fields
          ((a
            (Inter (lhs (Type_variable 5))
             (rhs
              (FunctionType (param (Type_variable 4)) (body (Type_variable 3))))))))))))
     (rhs (RecordType (fields ((b (Type_variable 4))))))))
   (body (Type_variable 3))) |}]

let%expect_test _ = 
  run_type_test {| (lam (name f) (body (app (lhs (var f)) (rhs (var f))))) |};
  (* ('b ^ ('b -> 'r)) -> 'r *)
  [%expect {|
    (FunctionType
     (param
      (Inter (lhs (Type_variable 6))
       (rhs (FunctionType (param (Type_variable 6)) (body (Type_variable 7))))))
     (body (Type_variable 7))) |}]

let%expect_test _ = 
  run_type_test {| (lam (name f) (body (app (lhs (sel (field g) (rcv (var f)))) (rhs (var f))))) |};
  (* ('b ^ {g : 'b -> 'r)} -> 'r *)
  [%expect {|
    (FunctionType
     (param
      (Inter (lhs (Type_variable 8))
       (rhs
        (RecordType
         (fields
          ((g
            (Inter (lhs (Type_variable 10))
             (rhs
              (FunctionType (param (Type_variable 8)) (body (Type_variable 9))))))))))))
     (body (Type_variable 9))) |}]