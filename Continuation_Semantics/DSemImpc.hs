
-----------------------------------------------------------------------------
--
-- ----------------------------------------------	--
-- Continuation semantics definitions: in Haskell	--
-- ----------------------------------------------	--
--
-----------------------------------------------------------------------------
module DSemImpc where

import Text.Show.Functions
-- --------------------------------------------	--
-- ============================================ --
-- ---------- Abstract Syntax -----------------	--

			-- terminal nodes of the syntax --
type      Numeral  = Int
type      Ident    = String

			-- parsed phrases of the abstract syntax --
data Command =
              Skip
            | Assign   Ident       Expression
            | Letin    Declaration Command
            | Cmdcmd   Command     Command
            | Ifthen   Expression  Command Command
            | Whiledo  Expression  Command
            | InvokeProc Ident ActualParameter
            | ForLoop Expression  Command
            deriving Show

data Expression =
            Num    Numeral
    	    | False_
    	    | True_
    	    | Notexp  Expression
    	    | Id      Ident
    	    | Sumof   Expression  Expression
    	    | Subof   Expression  Expression
    	    | Prodof  Expression  Expression
    	    | Less    Expression  Expression
            | Leten   Declaration Expression
            | InvokeFun Ident ActualParameter
            | PairExp  Expression Expression
		    | Fst Expression
		    | Snd Expression
            deriving Show

data Declaration =
	      Constdef Ident  Expression
	    | Vardef   Ident  TypeDef
	    | Fun Ident FormalParameter Expression
	    | Proc Ident FormalParameter Command
	    deriving Show

data TypeDef =
	      Bool | Int
	      deriving Show

data Program = Prog Ident Command

-- ---------- Semantic Domains ----------------	--

type	Integer	= Int
type	Boolean	= Bool
type	Location	= Int
-- data    Halt = Halt deriving (Show)
data	Value	= IntValue    Int
		        | TruthValue  Bool
		        | PairValue Value Value
                  deriving (Eq, Show, Ord)

type	Storable  = Value
data    Answer = Stble Storable
               | Halt
               | Output (Value, Answer)
               deriving (Show)


data	Bindable  = Const Value
                  | Variable Location
                  | BFunction Function
                  | Answer Answer
                  | BProcedure Procedure
                  deriving (Show)

data	Denotable = Unbound | Bound Bindable
                  deriving (Eq, Show)

data Sval  = Stored Storable | Undef | Unused

-- The actual storage in a Store
type DataStore = Location ->  Sval

--	                 --bot---   --top---  --data---
data Store = Store (Location,  Location,  DataStore)
type Environ  =  Ident -> Denotable
type Econt = Value -> Answer
type Ccont = Store -> Answer
type Dcont = Environ -> Store -> Answer

instance Eq Bindable where
  (BFunction f1) == (BFunction f2) = False
  (Const c1)     == (Const c2) = c1==c2
  (Variable l1)  == (Variable l2) = l1 == l2
  (BProcedure p1) == (BProcedure p2) = False


-- --------Function and Procedure
type FormalParameter = (Ident, TypeDef) -- [[ Const I: T]] in book
type ActualParameter = Expression


type Function =  Argument -> Store -> Answer
type Procedure = Argument -> Store -> Answer

type Argument = Bindable

bind_parameter :: FormalParameter -> Argument -> Environ
bind_parameter (ident,  typedef ) arg = bind (ident, arg )


give_argument ::  ActualParameter -> Environ ->Store -> Argument
give_argument e env sto = Answer (evaluate e env kont_null sto)

-- give_argument_p :: ActualParameter -> Environ -> Ccont -> Store -> Argument
-- give_argument_p e env cc sto = Answer (evaluate e env cc sto)

-- ---------- Semantic Functions --------------	--
run :: Program -> Int ->  Answer

-- valuation :: Int         -> Value
evaluate  :: Expression  -> Environ -> Econt -> Store ->  Answer
elaborate :: Declaration -> Environ -> Dcont -> Store ->  Answer
execute   :: Command     -> Environ -> Ccont -> Store ->  Answer
-- --------------------------------------------	--
-- ---------- Auxiliary Semantic Functions ----	--
add   (x, y) = x + y
diff  (x, y) = x - y
prod  (x, y) = x * y
lessthan  (x, y) = x < y

-- --------------------------------------------	--
-- ---------- Semantic Functions --------------	--
                          ---- some convienences..
kont_null :: Econt
kont_null v  = Output(v,Halt)

                          -- maybe this should dump the store?
cont_null :: Ccont
cont_null  = \any_store -> output_cont any_store

qont_null :: Dcont
qont_null  = \any_env -> cont_null

input, result :: Expression
input  = Id "input"       -- a shorthand..
result = Id "result"

                          -- dump the store....
dump :: Store -> [Value]
dump (sto @ (Store(lo, hi, datas) ) ) =
      map (curry fetch sto) [lo .. hi]

outVal :: Value -> String
outVal (IntValue   i) = "Integer" ++ show i
outVal (TruthValue b) = "boolean" ++ show b

outVals :: [Value] -> [String]
outVals xs = map outVal xs ++ ["\n"]

prints :: [Value] -> IO()
prints vs = print (outVals vs)

{- -- if you want the values on separate lines, then:
outVals = map outVal
prints  = putStr . unlines . outVals
-}

-- a continuation to dump the store....
dump_cont sto = do prints (dump sto)
                   return Halt

-- a continuation to output the store....
output_cont :: Store -> Answer
output_cont (sto @ (Store(lo, hi, dat)) ) =
    let put []     = Halt
        put (v:vs) = Output(v, put vs)
    in  put (dump sto)

{- ========== --
-- a continuation to output the store....
-- output_cont sto = reduce ( output oo pair ) Halt (dump sto)
output_cont :: Store -> Answer
output_cont sto = foldl (curry Output) Halt (dump sto)
 --}

-- =============================================== --
-- ------------------------------------------------
update :: (Store, Location, Value) -> Store
update (Store(bot,top,sto), loc, v) =
	let new adr = if adr==loc
			      then Stored v else (sto adr)
	in Store( bot, top, new)

		-- fetch from store, and convert into Storable (=Const)
fetch ::(Store,Location) -> Storable
fetch  (Store(bot,top,sto), loc)  =
	let stored_value(Stored stble) = stble
	    stored_value(Unused)       = error ("Store: Unused")
	    stored_value(Undef)        = error ("Store: Undefined ")
	in  stored_value(sto loc)

		-- create a new "undefined" location in a store
allocate :: Store -> (Store, Location)
allocate ( Store(bot,top,sto) )  =
	let newtop  = top+1
	    new adr = if adr==newtop
			      then Undef else (sto adr)
	in (Store( bot, newtop, new), newtop)

	-- ---------- Initialize system  ----------
env_null :: Environ
env_null =  \i -> Unbound

--  store_null =  empty (=0), addressing starts at 1
sto_init :: DataStore
sto_init =  \loc -> Unused

sto_null :: Store
sto_null =  Store( 1, 0, sto_init)

-- =============================================== --
--    coerce a Bindable into a Const..
coerc :: (Store, Bindable) -> Value
coerc (sto, Const v)      = v
coerc (sto, Variable loc) = fetch(sto,loc)
-- coerc (sto, BFunction function) =
coerc (sto, (Answer (Stble storable) ))= storable



-- ---------- Envirionment   ----------


bind :: (Ident,Bindable) -> Environ
bind  (name, val) =  \id -> if id==name
                            then Bound(val) else Unbound
-- look through the layered environment bindings
find :: (Environ, Ident) -> Bindable
find  (env, id)  =
	let getbv(Bound bdbl) = bdbl
	    getbv(Unbound)    = error ("undefined: " ++ id)
	in getbv( env id)

overlay :: (Environ, Environ) -> Environ
overlay  (env', env)  =
	\id -> let val = env' id
	       in  if val/=Unbound then val
	                            else env id

evaluate ( Num(n)  )  env ec sto  = ec (IntValue n)
evaluate ( True_   )  env ec sto  = ec (TruthValue  True)
evaluate ( False_  )  env ec sto  = ec (TruthValue  False)

     			-- lookup id, and  coerce as needed
evaluate ( Id(n)  )  env ec sto  = ec (coerc( sto, find(env,n) ))

     			-- get Consts, and compute result

evaluate ( Less e1 e2) env ec sto =
		evaluate e1 env ec1 sto
			where ec1 (IntValue val1) = evaluate e2 env ec2 sto
					where ec2 (IntValue val2) = ec (TruthValue (lessthan (val1, val2)))

evaluate ( Sumof e1 e2 ) env ec sto =
    evaluate e1 env ec1 sto
        where ec1 (IntValue val1) = evaluate e2 env ec2 sto
                where ec2 (IntValue val2) = ec (IntValue (add (val1, val2)))

evaluate ( Subof e1 e2 ) env ec sto =
    evaluate e1 env ec1 sto
        where ec1 (IntValue val1) = evaluate e2 env ec2 sto
                where ec2 (IntValue val2) = ec (IntValue (diff (val1, val2)))

evaluate (Prodof e1 e2 ) env ec sto =
    evaluate e1 env ec1 sto
        where ec1 (IntValue (val1)) = evaluate e2 env ec2 sto
                where ec2 (IntValue (val2)) = ec (IntValue ((prod (val1,val2))))

evaluate ( Leten def e ) env ec sto =
    elaborate def env dc sto
        where dc env' sto' = evaluate e (overlay (env',env)) ec sto'

evaluate ( InvokeFun ident  ap ) env ec sto =
        let BFunction fun = find (env, ident) in
        let arg = give_argument (ap) env sto

        in fun arg sto

{-
mileko
-------
elaborate (Fundef(name, fp, e)) env dcont sto =
    let func arg = evaluate e (overlay (parenv, env))
            where parenv = bindParameter fp arg
    in  dcont (bind(name, Func func)) sto

evaluate (InvokeFunc(ident, param)) env econt sto =
    let econt' arg = func arg econt sto
            where Func func = find(env, ident)
    in  giveArgument param env econt' sto
    
-}
-- pair value

evaluate (PairExp e1 e2) env ec sto =
        evaluate e1 env ec1 sto
            where ec1 val1 = evaluate e2 env ec2 sto
                    where ec2 val2 = ec (PairValue val1 val2)

evaluate (Fst e) env ec sto =
        evaluate e env ec1 sto
            where ec1 (PairValue val1 val2) = ec val1

evaluate (Snd e) env ec sto =
        evaluate e env ec1 sto
            where ec1 (PairValue val1 val2) = ec val2

elaborate ( Proc ident  fp  cmd) env dc sto =
        let proc arg sto1 =
                let env1 = bind_parameter fp arg
                in  execute (cmd) (overlay(env1,env)) cont_null sto1
        in dc (bind(ident, BProcedure proc)) sto

elaborate ( Fun ident fp  e ) env dc sto =
			let func arg sto' =
							let parenv = bind_parameter fp arg
							in  evaluate e (overlay (parenv,env)) kont_null sto'
			in dc (bind (ident, BFunction func)) sto

elaborate ( Constdef name e ) env dc sto =
     	evaluate e env ec1 sto
		    where ec1 val1 = dc (bind (name, Const  val1)) sto

elaborate ( Vardef name tdef ) env dc sto =
     	let (sto',loc) = allocate sto
		  in  dc  (bind(name, Variable loc)) sto'

-- execute -- command

execute ( Assign ident e) env cc sto =
    evaluate e env ec sto
        where
        	Variable loc = find (env, ident)
        	ec val = cc (update (sto,loc, val))

execute ( Letin def c ) env cc sto =
			elaborate def env dc sto
					where
						dc env1 sto1 = (execute c (overlay (env1,env)) cc sto1)

execute (Ifthen e cmd1 cmd2) env cc sto =
		evaluate e env ec sto
				where
					ec val = if val== (TruthValue True)
									 then execute cmd1 env cc sto
									 else execute cmd2 env cc sto


execute (Cmdcmd cmd1 cmd2) env cc sto =
		execute cmd1 env cc1 sto
				where
					cc1 sto1 = execute cmd2 env cc sto1


execute (Whiledo e cmd) env cc sto =

		cc1 sto
				where
					cc1 s = evaluate e env ec s
							where
								ec val = if val == (TruthValue True)
												 then execute cmd env cc1 s
												 else cc s

execute (InvokeProc ident ap) env cc sto =
        let BProcedure proc = find (env, ident) in
        let arg = give_argument  ap env sto
        in proc arg sto

execute (ForLoop e cmd) env cc sto = 
        evaluate e env ec sto
          where 
            ec (IntValue v) = forrange v env cc sto
                where 
                    forrange v env cc sto1 = if (v > 0) 
                                             then execute cmd env cc1 sto1
                                             else cc sto1
                         where cc1 sto2 = forrange (v-1) env cc sto2
                         
-- program --

run (Prog i command) input =
    execute command env cont_null sto2
        where
            sto = sto_null
            (sto1,loc) = allocate sto
            env = overlay(bind( i, Variable loc),env)
            sto2 = update (sto1,loc,(IntValue input))
            Variable loc1 = find (env,i)
            -- cc s = Stble (fetch (s, loc1))


