type ide = string;;
(*chiave: int o string*)
type key = KInt of int | KString of string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Mod of exp * exp | Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | 
	FunCall of exp * exp | Letrec of ide * exp * exp 
	| Dictionary of (key * exp) list
	| Insert of key * exp * exp
	| Delete of key * exp
	| HasKey of key * exp
	| Filter of key list * exp
	| Iterate of exp * exp
	| Fold of exp * exp
;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun 
	| DicVal of (key * evT) list
	and evFun = ide * exp * evT env;;

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true 
		| _ -> false) 
	| "bool" -> (match v with
		Bool(_) -> true 
		| _ -> false)
	| _ -> failwith("not a valid type");;

let keytype (k: key) : string = match k with
	 KInt(_) -> "int"
	 | KString(_) -> "string";;

let valuetype (v: evT) : string = match v with
	Int(_) -> "int"
	| Bool(_) -> "bool"
	| _ -> failwith("Valore non ammesso");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u)
		| _ -> failwith("Type error"))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u)
		| _ -> failwith("Type error"))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u)
		| _ -> failwith("Type error"))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u)
		| _ -> failwith("Type error"))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n)
	    | _ -> failwith("Type error"))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0)
		| _ -> failwith("Type error"))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e))
		| _ -> failwith("Type error"))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e)
		| _ -> failwith("Type error"))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false)
		| Bool(false) -> Bool(true)
		| _ -> failwith("Type error"))
	else failwith("Type error");;

let mdl x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n mod u)
		| _ -> failwith("Type error"))
	else failwith("Type error");;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Mod(a, b) -> mdl (eval a r) (eval b r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
    Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
            		_ -> failwith("non functional def"))

    | Dictionary(l) -> (
    	match l with
    		[] -> DicVal([]) 
    		| (k, e)::t -> let tpk = keytype k in
    			let tpv = valuetype (eval e r) in 
					DicVal(evalDic l r tpk tpv [])
    	) 

    | Insert(k, e, d) -> (
    	match eval d r with
    		DicVal(l) -> ( 
    			let v = eval e r in 
	    			match l with
    					[] -> DicVal(insert k v l)
    					| (k1, v1)::t -> if(((keytype k)=(keytype k1))&&((valuetype v)=(valuetype v1)))
    						then DicVal(insert k v l)
    						else failwith("Type error")
    		)
    		| _ -> failwith("Not a dictionary")
    )
    
    (*Delete non controlla il tipo della chiave: se è sbagliato non succede niente*)
    | Delete(k, d) -> (
    	match eval d r with
    		DicVal(l) -> DicVal(delete k l)
    		| _ -> failwith("Not a dictionary")
    	)
    
    | HasKey(k, d) -> (
    	match eval d r with
    		DicVal(l) -> haskey k l
    		| _ -> failwith("Not a dictionary")
    	)

    | Filter(kl, d) -> (
    	match eval d r with
    		DicVal(l) -> DicVal(filter kl l)
    		| _ -> failwith("Not a dictionary")
    )

    | Iterate(f, d) -> let fClosure = eval f r in (
    	match fClosure with
    		FunVal(arg, fBody, fDecEnv) -> (
    			match eval d r with
    				DicVal(l) -> DicVal(iterate arg fBody fDecEnv l)
    				| _ -> failwith("Not a dictionary")
		    )
		    | _ -> failwith("Not a function")
	)

	| Fold(f, d) -> let fClosure = eval f r in (
    	match fClosure with
    		FunVal(arg, fBody, fDecEnv) -> (
    			match eval d r with
    				DicVal(l) -> fold arg fBody fDecEnv (Int(0)) l
    				| _ -> failwith("Not a dictionary")
		    )
		    | _ -> failwith("Not a function")
	)

	and evalDic (l: (key * exp) list) (r: evT env) (tpk: string) (tpv: string) (d: (key * evT) list) : (key * evT) list =
		match l with
			[] -> d
			| (k, e)::t -> let v = (eval e r) in 
				let tv = valuetype v in
					let tk = keytype k in 
						(if( (tv=tpv) && (tk=tpk) ) then evalDic t r tpk tpv (insert k v d)
													else failwith("Lista non omogenea"))

	and insert (k: key) (v: evT) (l: (key * evT) list) : (key * evT) list =
		match l with
			[] -> [(k, v)]
			| (k1, v1)::t -> if k1=k then failwith("Key already exists")
									 else (k1, v1)::insert k v t

	and delete (k: key) (l: (key * evT) list) : (key * evT) list =
		match l with
			[] -> []
			| (k1, v1)::t -> if k1=k then t
									 else (k1, v1)::delete k t

	and haskey (key: key) (l: (key * evT) list) : evT =
		match l with
			[] -> Bool(false)
			| (k, v)::t -> if k=key then Bool(true)
									else haskey key t 

	and filter (kl: key list) (l: (key * evT) list) : (key * evT) list =
		match l with
			[] -> []
			| (k, v)::t -> if search k kl then (k, v)::filter kl t 
								 		  else filter kl t

	(*funzione ausiliaria per filter*)
	and search (key: key) (l: key list) : bool =
		match l with
			[] -> false
			| k::t -> if k=key then true
							   else search key t 

	and iterate (arg: ide) (fBody: exp) (fDecEnv: evT env) (l: (key * evT) list) : (key * evT) list =
		match l with
			[] -> []
			| (k, v)::t -> (k, eval fBody (bind fDecEnv arg v))::iterate arg fBody fDecEnv t

	and fold (arg: ide) (fBody: exp) (fDecEnv: evT env) (n: evT) (l: (key * evT) list) : evT =
		match l with
			[] -> n
			| (k, v)::t -> fold arg fBody fDecEnv (sum n (eval fBody (bind fDecEnv arg v))) t 
;;
