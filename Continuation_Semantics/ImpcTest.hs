
module ImpcTest where

import DSemImpc

-- --------------------------------------------	--
-- ============================================ --
-- ---------- Test it..! ---------------------- --


e1 = Num 2
e2 = Sumof (Num 1) (Num 2)

-- Trace_flag = "Test: expressions    [ 2, 1+2]"
a1 = evaluate e1 env_null kont_null sto_null;        --  = 2
a2 = evaluate e2 env_null kont_null sto_null;        --  = 3

-- Trace_flag = "Test: expressions    [ 1+2*3 = 7 ]"
a3 = evaluate (Sumof (Num 1) (Prodof (Num 2) (Num 3)))
                        env_null kont_null sto_null; --  = 7

test1() = do print "test1():---: expressions  [ 2, 1+2, 1+2*3 ]"
             print a1
             print a2
             print a3
-- ------------------------- --
dx = Constdef "x" (Num 2)      -- a declaration --
a4 = elaborate dx env_null qont_null sto_null


a5 = evaluate (  Leten  dx (Sumof (Num 1) (Id "x") ) )
                        env_null kont_null sto_null; -- = 3

test2() = do print "test2():---: declaration   {const x = 2}"
             print a4
             print a5
-- =============================================== --
--   result := input


-- input1 = Num(1)
pgm1 = Prog ("I") (Assign "I" (Id "I"))

                        -- run the program on an input --
test3() = do print "test3():---: {result = input}  [1, 2]"
             print (run pgm1  1)
             print (run pgm1  2)




-- =============================================== --
--   result := input + 1
--
pgm2 = Prog   ("I")  ( Assign "I" (Sumof (Num 1) (Id "I") ) )

                        -- run the program on inputs --
test4() = do print "test4():---: {result = input+1}  [2, 3]"
             print $ run pgm2  1
             print $ run pgm2  2


{- -----------------------------------------------
 *   let value x ~ 2
 *   in let var y : int
 *      in  y:= 3
 *          if x<y then y:=1
 *                 else y:=2
 --}

-- Note that we do no output, so need to dump store for


cmd' =
  Letin  (Constdef "x" (Num 2))
         (Letin (Vardef "y" Int)
                (Cmdcmd (Assign "y" (Num 3))
                        (Ifthen (Less (Id "x") (Id "y"))
                                (Assign "y" (Num 1))
                                (Assign "y" (Num 2))
                                )
                        )
                )

cmd =
  Letin (Constdef "x" (Num 2))
        (Letin (Vardef "y" Int)
               (Cmdcmd (Assign "y" (Num 3))
                       (Assign "y" (Num 1))
                       )
                )

                -- get Answer --
a9  = execute cmd  env_null   cont_null    sto_null

                -- get a full set Answers..!  --
a9b  = execute cmd  env_null  output_cont   sto_null


test5() = do print "test5():---: Simple Program.2  -> [1]"
             -- trace("Pre-a9") print "Pre-a9"
             print a9
             print a9b
             print $ run (Prog ("y") cmd) 000

{- --------------------------------------------------------
 *   let Const  x ~ 2
 *   in let var y : int
 *      in y := 3
 *         let var z : int
 *         in  z := 0
 *             z := z+1
 --}
x    = Id "x"      -- some shorthands...
y    = Id "y"
z    = Id "z"
zero = Num 0
one  = Num 1

cmd3 =
  Letin (Constdef "x" (Num 2))
        (Letin (Vardef "y" Int)
               (Cmdcmd (Assign "y" (Num 3))
                       (Letin (Vardef "z" Int)
                              (Cmdcmd (Assign "z" zero)
                                      (Assign "z" (Sumof z one))                                      )
                       )
                )
         )

a10a = execute cmd3  env_null   cont_null  sto_null
a10b = execute cmd3  env_null output_cont  sto_null

test6() = do print "test6():---: Simple Program.3  -> [3,1]"
             -- print (run (Prog cmd3) 0)
             print a10b

{- --------------------------------------------------------
 *   // a loop
 *   let Const  x ~ 2
 *   in let var y : int
 *      in y := 3
 *         let var z : int
 *         in  z:= 0            { multiply z = x*y }
 *             while 0<y do  z := z+x; y := y-1
 --}
cmd4 =
  Letin (Constdef "x" (Num 2))
        (Letin  (Vardef "y" Int)
                (Cmdcmd (Assign "y" (Num 3))
                        (Letin (Vardef "z" Int)
                               (Cmdcmd (Assign "z" zero)
                                       (Whiledo (Less zero y)
                                         (Cmdcmd (Assign "z" (Sumof z x  ))
                                                 (Assign "y" (Subof y one))
                                                  )
                                        )
                                )
                         )
                 )
         )

a11a = execute cmd4  env_null   cont_null  sto_null
a11b = execute cmd4  env_null output_cont  sto_null

test7() = do print "test7():---: Simple Program.4  -> [0,6, Halt]"
             -- print $ run (Prog cmd4) 0
             -- print a11a
             print a11b
-- --------------------------------------------------------
-- function ---------------
-- exp_body = Sumof (Id("ident"))  Id("ident")
exp_body = Num(1)
dec_fun = Fun "function1" ("ident", Int)  exp_body
arg = Num(9)
evaluate_function = (InvokeFun "function1"  arg)
f1 = evaluate ( Leten dec_fun evaluate_function ) env_null kont_null sto_null



exp2_body = Sumof (Id("ident")) (Id("ident"))
dec2_fun = Fun "function1" ("ident", Int) exp2_body
arg2 = Num(9)
evaluate2_function = (InvokeFun "function1" arg2)
f2 = evaluate (Leten dec2_fun evaluate2_function) env_null kont_null sto_null


test8() = do print "test8(): function invoke  -- "
             print f1
             --print f2


-- procedure

--p_cmd2 = Letin (Vardef "output" Int) (Assign "output"  (Sumof (Id("ident"))  (Id("ident"))))

p_cmd2 = Letin (Vardef "output" Int) (Assign "output" (Num(8)) )
p_decl3 = Proc "procedure1" ("ident", Int) p_cmd2
p_cmd3 = InvokeProc "procedure1" (Num(4))
p_sto3 = execute (Letin p_decl3 p_cmd3) env_null cont_null sto_null
p1 = p_sto3


test9() = do print " test9(): procedure invoke--"
             print p1


-- pair-----------
first = evaluate (Fst (PairExp (Num(1)) (Num(2)))) env_null kont_null sto_null
second = evaluate (Snd (PairExp (Num(1)) (Num(2)))) env_null kont_null sto_null

test10() = do print "Pair data structure Fst and Snd Pair(1,2)"
              print first
              print second
              
flc1 = (Letin (Vardef "y" Int) (Assign "y" zero))
a12a = execute (ForLoop (Num 5) flc1) env_null cont_null sto_null
test11() = do print "test11():---: ForLoop Command  -> store 5 zeros and halt"
              print a12a
-- ==== Tests::

-- impcAns = [ a1, a2, a3a, a4, a5, a6, a7, a8 ]
-- impcAns = [ a1, a2, a3, a4, a6, a7]

impcTests = do print "------ APL:: DSem_impc"
               test1()   -- Expressions
               test2()   -- Declarations
               test3()   -- Expressions
               test4()   -- Expressions
               test5()   -- simple program.2
               test6()   -- simple program.3
               test7()   -- simple program.4
               test8()   -- function
               test9()   -- procedure
               test10()  -- Pair data structure
               test11()  -- ForLoop Command
               -- putStrLn $ draw e2

-- ============================================	 --
