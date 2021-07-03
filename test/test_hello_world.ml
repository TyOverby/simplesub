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
  run_type_test {| 5 |};
[%expect {| (PrimitiveType int) |}]

let%expect_test _ = 
  run_type_test {| (lam a a) |};
[%expect {| (FunctionType (param (Type_variable 0)) (body (Type_variable 0))) |}]

let%expect_test _ = 
  run_type_test {| (record (a 5) (b 10)) |};
[%expect {| (RecordType (fields ((a (PrimitiveType int)) (b (PrimitiveType int))))) |}]

let%expect_test _ = 
  run_type_test {| (record (a (lam a a)) (b 10)) |};
[%expect {|
  (RecordType
   (fields
    ((a (FunctionType (param (Type_variable 1)) (body (Type_variable 1))))
     (b (PrimitiveType int))))) |}]

let%expect_test _ = 
  run_type_test {| (lam a ((. a a) (. a b))) |};
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
  run_type_test {| (lam f (f f)) |};
  (* ('b ^ ('b -> 'r)) -> 'r *)
  [%expect {|
    (FunctionType
     (param
      (Inter (lhs (Type_variable 6))
       (rhs (FunctionType (param (Type_variable 6)) (body (Type_variable 7))))))
     (body (Type_variable 7))) |}]

let%expect_test _ = 
  run_type_test {| ((lam f (f f)) (lam a a)) |};
  [%expect {| (Type_variable 8) |}]

let%expect_test _ = 
  run_type_test {| (lam f ((. f g) f)) |};
  (* ('b ^ {g : 'b -> 'r)} -> 'r *)
  [%expect {|
    (FunctionType
     (param
      (Inter (lhs (Type_variable 12))
       (rhs
        (RecordType
         (fields
          ((g
            (Inter (lhs (Type_variable 14))
             (rhs
              (FunctionType (param (Type_variable 12)) (body (Type_variable 13))))))))))))
     (body (Type_variable 13))) |}]

