
-- ----------------------------------------------	--
-- denotational semantics definitions: in Haskell	--
-- ----------------------------------------------	--
-- Imp: expressions language (Watt, Ex. 3.6)	--
--      with commands    (store).. 		--
--      and  definitions (evnironment).. 	--
--
--     (A nicer version of Ex. 4.7 from text)	--
-- --------------------------------------------	--
--
-----------------------------------------------------------------------------
module DSemImp2 where

import Text.Show.Functions

-- --------------------------------------------	--
-- ---------- Abstract Syntax -----------------	--

			-- terminal nodes of the syntax --
type      Numeral  = Int
type      Ident    = String

			-- parsed phrases of the abstract syntax --
data Command =
              Skip
            | Assign   (Ident,       Expression)
            | Letin    (Declaration, Command   )
            | Cmdcmd   (Command,     Command   )
            | Ifthen   (Expression,  Command, Command)
            | Whiledo  (Expression,  Command   )
            | For (Declaration, Expression, Expression, Command) -- for (i=0,5,1,cmd)
            | ForRange    (Numeral,Numeral,Numeral,Command)
            | InvokeProc (Ident, ActualParameter)
			 deriving (Show)

data Expression =
            Num    Numeral
    	    | False_
    	    | True_
    	    | Notexp   Expression
    	    | Id       Ident
    	    | Sumof   (Expression,  Expression)
    	    | Subof   (Expression,  Expression)
    	    | Prodof  (Expression,  Expression)
    	    | Less    (Expression,  Expression)
            | Leten   (Declaration, Expression)
		    | InvokeFun (Ident, ActualParameter)  -- for func
		    | PairExp  (Expression, Expression)
		    | Fst Expression
		    | Snd Expression
            deriving Show

data Declaration =
	      Constdef (Ident,  Expression)
	    | Vardef   (Ident,  TypeDef   )
		| Fun      (Ident, FormalParameter, Expression)
		| Proc     (Ident, FormalParameter, Command)
			deriving (Show)

data TypeDef =
	      Bool | Int | String
				deriving (Show)

-- --------------------------------------------	--
-- ---------- Semantic Domains ----------------	--

type	Integer	= Int
type	Boolean	= Bool
type	Location	= Int


data	Value	= IntValue    Int
		        | TruthValue  Bool
		        | PairValue (Value, Value)
                  deriving (Eq, Show, Ord)

type	Storable  = Value

data	Bindable  = Const Value
				  | Variable Location
				  | Value Value
				  | BFunction Function
				  | BProcedure Procedure
				  deriving (Show)


data	Denotable = Unbound | Bound Bindable
                   deriving (Eq)


instance Eq Bindable where
  (BFunction f1) == (BFunction f2) = False
  (BProcedure p1)== (BProcedure p2) = False
  (Const c1)     == (Const c2) = c1==c2
  (Value v1)     == (Value v2) = v1 == v2
  (Variable l1)  == (Variable l2) = l1 == l2
-- --------------------------------------------	--
-- ---------- Semantic Functions --------------	--
valuation :: Int         -> Value
evaluate  :: Expression  -> Environ -> Store ->  Value
elaborate :: Declaration -> Environ -> Store ->  (Environ,Store)
execute   :: Command     -> Environ -> Store ->  Store

-- --------------------------------------------	--
-- ---------- Auxiliary Semantic Functions ----	--
add   (x, y) = x + y
diff  (x, y) = x - y
prod  (x, y) = x * y

lessthan  (x, y) = x < y

-- --------Function and Procedure
type FormalParameter = (Ident, TypeDef) -- [[ Const I: T]] in book
type ActualParameter = Expression


type Function =  Argument -> Store -> Value
type Procedure = Argument -> Store -> Store

type Argument = Bindable

bind_parameter :: FormalParameter -> Argument -> Environ
bind_parameter (ident,  typedef ) arg = bind (ident, arg )


give_argument ::  ActualParameter -> Environ -> Store -> Argument
give_argument e env sto = Value (evaluate e env sto)

-- ---------- Storage   ---------- --
-- fun deallocate sto loc:Location = sto	-- ... later --

data Sval  = Stored Storable | Undef | Unused

-- The actual storage in a Store
type DataStore = Location -> Sval

--	                 --bot---   --top---  --data---
data Store = Store (Location,  Location,  DataStore)

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

					-- dump the store....

dump :: Store -> [Value]
dump (sto @ (Store(lo, hi, dat)) ) =

    map (curry fetch sto) [lo .. hi]

-- ---------- Envirionment   ----------
type  Environ  =  Ident -> Denotable

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

-- ---------- Etc...
--    coerce a Bindable into a Const..
coerc :: (Store, Bindable) -> Value
coerc (sto, Const v)      = v
coerc (sto, Value v)      = v
coerc (sto, Variable loc) = fetch(sto,loc)

-- ---------- Initialize system  ----------
env_null :: Environ
env_null =  \i -> Unbound

--  store_null =  empty (=0), addressing starts at 1
sto_init :: DataStore
sto_init =  \loc -> Unused

sto_null :: Store
sto_null =  Store( 1, 0, sto_init)

-- --------------------------------------------
-- ---------- Semantic Equations --------------

				-- from integer to Const Value
valuation ( n ) = IntValue(n)

execute ( Skip ) env sto = sto

execute ( Assign(name,exp) ) env sto  =
     		let rhs = evaluate exp env sto
     		    Variable loc = find( env,name)
     		in  update( sto, loc, rhs)

execute ( Letin(def,c) ) env sto =
			let (env' , sto') = elaborate def env sto
			in 	execute c (overlay (env',env)) sto'

     		-- ...

execute ( Cmdcmd(c1,c2) ) env sto  =
			let sto' = execute c1 env sto
			in execute c2 env sto'
     		-- ...

execute ( Ifthen(e,c1,c2) ) env sto =

			let v1 = evaluate e env sto
			in if v1 == TruthValue(True)
				 then execute c1 env sto
				 else execute c2 env sto
     		-- ...

execute ( Whiledo(e,c) ) env sto =
     	let executeWhile env sto =
							if evaluate e env sto == TruthValue True
							then executeWhile env (execute c env sto)
							else sto
	     in executeWhile env sto

execute (ForRange(start,end,incr,c)) env sto =
                let for start env sto = if( start + incr < end )
                                         then for (start+incr) env (execute c env sto)
                                         else sto
                in
                    for start env sto
-- for (i=0; 4; 1;cmd)

execute (For (Constdef (ident,  exp0), e1, e2, cmd) ) env sto =
			let IntValue incr = evaluate e2 env sto in
			let IntValue end = evaluate e1 env sto in
			let (env',sto') = elaborate (Constdef (ident, exp0)) env sto in
			let Const (IntValue(start)) = find (env', ident) in
			let executeFor start env1 sto1 = if (start < end)
                                             then
                                                  let env2 = bind(ident,(Const(IntValue(start)))) in
                                                    executeFor (start+incr) (overlay(env2,env1)) (execute cmd (overlay(env2,env1)) sto1)
                                             else sto1
			in executeFor start (overlay(env',env)) sto'



execute (InvokeProc (ident, ap)) env sto =
        let BProcedure proc = find (env, ident) in
        let arg = give_argument  ap env sto
        in proc arg sto
     			-- simple, just build a Const
evaluate ( Num(n)  )  env sto  = IntValue n
evaluate ( True_   )  env sto  = TruthValue  True
evaluate ( False_  )  env sto  = TruthValue  False

     			-- lookup id, and  coerce as needed
evaluate ( Id(n)  )  env sto  = coerc( sto, find(env,n) )

     			-- get Consts, and compute result
evaluate ( Sumof(e1,e2) ) env sto =
     	let IntValue i1 = evaluate e1 env sto
     	    IntValue i2 = evaluate e2 env sto
     	in  IntValue  ( add(i1,i2) )

evaluate ( Subof(e1,e2) ) env sto =
     	let IntValue i1 = evaluate e1 env sto
     	    IntValue i2 = evaluate e2 env sto
     	in  IntValue  ( diff(i1,i2) )

evaluate ( Prodof(e1,e2) ) env sto =
     	let IntValue i1 = evaluate e1 env sto
     	    IntValue i2 = evaluate e2 env sto
     	in  IntValue  ( prod(i1,i2) )
     		-- ...

evaluate ( Less(e1,e2) ) env sto =
     	let v1 = evaluate e1 env sto in
			let	v2 = evaluate e2 env sto
			in  if v1 < v2
					then TruthValue (True)
					else TruthValue (False)
-- pair value

evaluate (PairExp( e1, e2)) env sto =
        let val1 = evaluate e1 env sto in
        let val2 = evaluate e2 env sto
        in  PairValue (val1, val2)

evaluate (Fst e) env sto =
        let PairValue (val1, val2) = evaluate e env sto
        in  val1

evaluate (Snd e) env sto =
        let PairValue (val1, val2) = evaluate e env sto
        in  val2


evaluate ( InvokeFun(ident , ap) ) env sto =
        let BFunction fun = find (env, ident) in
        let arg = give_argument (ap) env sto

        in fun arg sto

-- layer environment, and compute result
evaluate ( Leten(def,e) ) env sto =
     	let (env', sto') = elaborate def env sto
		in  evaluate e (overlay (env', env)) sto'


elaborate ( Constdef(name,e) ) env sto =
     	let v = evaluate e env sto
		in  ( bind(name, Const  v), sto )

elaborate ( Vardef(name,tdef) ) env sto =
     	let (sto',loc) = allocate sto
		in  ( bind(name, Variable loc), sto' )

elaborate ( Fun (ident, fp , e) ) env sto =
			let func arg sto' =
							let parenv = bind_parameter fp arg
							in  evaluate e (overlay (parenv,env)) sto'
			in (bind (ident, BFunction func), sto)


elaborate ( Proc(ident, fp, cmd)) env sto =
        let proc arg sto1 =
                let env1 = bind_parameter fp arg
                in  execute(cmd) (overlay(env1,env)) sto1
        in (bind(ident, BProcedure proc) , sto)
