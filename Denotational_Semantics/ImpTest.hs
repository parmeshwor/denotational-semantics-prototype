-----------------------------------------------------------------------------
--
-- Module      :  :  Imp_tests
-- APL:: IMP DSem - Lab Tests
--
-- ----------------------------------------------	--
-- denotational semantics definitions: in Haskell	--
-- ----------------------------------------------	--
--
-----------------------------------------------------------------------------
module ImpTest where
import DSemImp2

-- ============================================	 --

-- ---------- Test it..! ----------------------	--



e1 = Num(2)

e2 = Sumof(Num(1),Num(2))

v1 = evaluate e1 env_null sto_null		--  = 2

v2 = evaluate e2 env_null sto_null		--  = 3



v3 = evaluate (Sumof(Num(1), Prodof(Num(2),Num(3)))) env_null sto_null --  = 7



dx  = Constdef("x",Num(2))	-- a declaration

dxx = elaborate dx env_null sto_null


pgm =

  Letin( Constdef( "x", Num(2)),

         Letin( Vardef( "y", Int),

		    Cmdcmd( Assign( "y", Num(3)),

		        Ifthen( Less(Id("x"),Id("y")),

			        Assign("y",Num(1)),

			        Assign("y",Num(2))

				)

			)

		)

         )

  

s1 = execute pgm  env_null sto_null



x_ = Id("x")	-- a shorthand...

y_ = Id("y")

z_ = Id("z")


pgm3 =

  Letin( Constdef( "x", Num(2)),

       Letin( Vardef( "y", Int),

              Cmdcmd( Assign( "y", Num(3)),

	              Letin ( Vardef( "z", Int),

		              Cmdcmd( Assign( "z",Num(0)),

                                      Assign("z", Sumof(z_,Num(1)))

				      )

			      )

		      )

	      )

       )

  

sto3 = execute pgm3  env_null sto_null


v5 = map (curry fetch sto3) [ 1, 2 ]

s2 = dump sto3


x = Id("x")	-- a shorthand...

y = Id("y")

z = Id("z")

pgm2 =

  Letin( Constdef( "x", Num(2)),

       Letin( Vardef( "y", Int),

              Cmdcmd( Assign( "y", Num(3)),

	              Letin ( Vardef( "z", Int),

		              Cmdcmd( Assign( "z",Num(0)),

                                      Whiledo( Less(Num(0),y_),

                                          Cmdcmd( Assign("z", Sumof(z_,x_)),

                                                  Assign("y", Subof(y_,Num(1)))

						  )

					  )

				      )

			      )

		      )

	      )

       )

  

sto2 = execute pgm2  env_null sto_null

s3 = dump sto2

-- function ---------------
exp_body = Sumof (Id("ident") , Id("ident"))
dec_fun = Fun("function1", ("ident", Int) , exp_body )
arg = Num(9)
evaluate_function = InvokeFun("function1" , arg)

f1 = evaluate (Leten (dec_fun, evaluate_function) ) env_null sto_null



-- -----procedure

p_cmd2 = Letin (Vardef ("output", Int),Assign ("output",(Sumof (Id("ident") , Id("ident"))) ))
p_decl3 = Proc ("procedure1", ("ident", Int), p_cmd2)
p_cmd3 = InvokeProc ("procedure1", Num(4))
p_sto3 = execute (Letin (p_decl3, p_cmd3)) env_null sto_null
p_p1 = dump p_sto3

-- pair-----------
first = evaluate (Fst (PairExp(Num(1),Num(2)))) env_null sto_null
second = evaluate (Snd (PairExp(Num(1),Num(2)))) env_null sto_null

-- loop-----------
flc1 = Letin( Vardef( "y", Int),
	Assign("y", Num(1))
       )
fl1 = ForRange (0, 3, 1, flc1)
frv = dump (execute fl1 env_null sto_null)

-- For loop
f_cmd = Letin(Vardef("x",Int),Assign("x", Id("ident")))
f_decl = Constdef ("ident",  Num(0))
f_val = execute (For(f_decl, Num(5), Num(1), f_cmd)) env_null sto_null
f_out = dump f_val
-- ----------------------------------
impTestVals = [ v1, v2, v3 ]
impTestStos = [ dump s1, s2, s3 ]
impTestFun  =  [f1]
impTestProc =  [p_p1]
impTestPair = [first, second]
impTestLoop = [f_out]
impTests = do print "------ APL:: DSem_imp"
              print "-- value --"
              print impTestVals
              print "-- store --"
              print impTestStos
              print "-- Function --f(9)=> 9+9 = 18"
              print impTestFun
              print "-- Procedure --p(4 => sum(4,4) = 8)"
              print impTestProc
              print "-- pair data structure fst snd of [1,2]--"
              print impTestPair
              print "-- for loop -- for (i=0;i<5;i++;cmd) => for (i=0;5,1,cmd) "
              print impTestLoop

-- ============================================	 --
