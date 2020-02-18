(* Test di Dictionary *)
let env0 : ide -> evT = emptyenv Unbound;;

(* Un dizionario vuoto *)
eval(Dictionary([])) env0;;

(* Un esempio di dizionario con chiavi di tipo KString e valori di tipo Eint *)
eval (Dictionary([(KString("mele"), Eint(430)); (KString("banane"), Eint(312)); 
	(KString("arance"), Eint(525)); (KString("pere"), Eint(217))])) env0;;

(* Un dizionario equivalente al primo *)
eval (Dictionary([(KString("mele"), Sum(Eint(400), Eint(30)));  
	(KString("banane"), Prod(Eint(312), Eint(1))); 
	(KString("arance"), Ifthenelse(Ebool(true), Eint(525), Eint(0))); 
	(KString("pere"), Eint(217))])) env0;;

(* Un esempio di dizionario con chiavi di tipo KInt e valori di tipo Ebool,
	che rappresenta gli studenti che hanno passato o no un esame *)
eval (Dictionary([(KInt(548279), Ebool(true)); (KInt(123456), Ebool(false)); 
	(KInt(987654), Ebool(true))])) env0;;

(* Un dizionario con chiavi non ammissibili *)
eval (Dictionary([(Ebool(true), Eint(24))])) env0;;

(* Un dizionario con chiavi duplicate *)
eval (Dictionary([(KString("mele"), Eint(430)); 
				  (KString("mele"), Eint(312))])) env0;;

(* Un dizionario con chiavi non omogenee *)
eval (Dictionary([(KInt(548279), Ebool(true)); 
				(KInt(123456), Ebool(false)); 
				(KString("mele"), Ebool(true))])) env0;;

(* Un dizionario con valori non omogenei *)
eval (Dictionary([(KString("mele"), Ebool(true)); 
				(KString("banane"), Eint(312)); 
				(KString("arance"), Eint(525)); 
				(KString("pere"), Eint(217))])) env0;;

(* ============================================================ *)
(* Test di Insert *)
let env0 : ide -> evT = emptyenv Unbound;;

(* Inserimenti validi *)
let env1 = bind env0 "Magazzino" (eval(Dictionary([])) env0);;
let env2 = bind env1 "Magazzino1" (eval (Insert(KString("mele"), Eint(430), Den("Magazzino"))) env1);;
let env3 = bind env2 "Magazzino2" (eval (Insert(KString("banane"), Eint(312), Den("Magazzino1"))) env2);;
applyenv env3 "Magazzino2";;

(* Inserimento di una chiave già esistente *)
eval (Insert(KString("banane"), Eint(100), Den("Magazzino2"))) env3;;

(* Inserimento di una chiave non valida *)
eval (Insert(KInt(1), Eint(100), Den("Magazzino2"))) env3;;

(* Inserimento di un valore non valido *)
eval (Insert(KString("arance"), Ebool(true), Den("Magazzino2"))) env3;;

(* ============================================================ *)
(* ============================================================ *)
(* Tutti i test successivi fanno riferimento al seguente dizionario, 
	se non diversamente specificato *)
let env0 : ide -> evT = emptyenv Unbound;;
let env1 = bind env0 "Magazzino" (eval (Dictionary([(KString("mele"), Eint(430)); 
	(KString("banane"), Eint(312)); (KString("arance"), Eint(525)); 
	(KString("pere"), Eint(217))])) env0);;
applyenv env1 "Magazzino";;
(* ============================================================ *)
(* ============================================================ *)
(* Test di Delete *)

(* Se la chiave non è nel dizionario non succede niente *)
eval (Delete(KString("ananas"), Den("Magazzino"))) env1;;
eval (Delete(KInt(5), Den("Magazzino"))) env1;;
eval (Delete(KString("banane"), Dictionary([]))) env1;;

(* Cancellazione corretta *)
eval (Delete(KString("pere"), Den("Magazzino"))) env1;;

(* ============================================================ *)
(* Test di HasKey *)

(* Restituisce true *)
eval (HasKey(KString("banane"), Den("Magazzino"))) env1;;

(* Restituiscono false *)
eval (HasKey(KString("ananas"), Den("Magazzino"))) env1;;
eval (HasKey(KInt(5), Den("Magazzino"))) env1;;
eval (HasKey(KString("banane"), Dictionary([]))) env1;;

(* ============================================================ *)
(* Test di Filter *)

(* Il dizionario risultante conterrà solo le chiavi "mele" e "pere" *)
eval (Filter([KString("pere"); KString("mele")], Den("Magazzino"))) env1;;

(* Restituiscono un dizionario vuoto *)
eval (Filter([], Den("Magazzino"))) env1;;
eval (Filter([KInt(5); KString("ananas")], Den("Magazzino"))) env1;;
eval (Filter([KString("mele"); KString("pere")], Dictionary([]))) env1;;

(* ============================================================ *)
(* Test di Iterate *)

(* Somma 1 ad ogni valore *)
eval (Iterate(Fun("x", Sum(Den("x"), Eint(1))), Den("Magazzino"))) env1;;

(* Sostituisce ogni valore v con true se v è pari, false altrimenti *)
eval (Iterate(Fun("x", Ifthenelse(Eq(Mod(Den("x"), Eint(2)), Eint(0)), Ebool(true), Ebool(false))), Den("Magazzino"))) env1;;

(* Inverte i valori di verità *)
let env2 = bind env0 "Studenti" (eval (Dictionary([(KInt(548279), Ebool(true));
	(KInt(123456), Ebool(false)); (KInt(987654), Ebool(true))])) env0);;
eval (Iterate(Fun("x", Not(Den("x"))), Den("Studenti"))) env2;;

(* ============================================================ *)
(* Test di Fold *)

(* Somma di tutti i valori aumentati di 1: 1488 *)
eval (Fold(Fun("x", Sum(Den("x"), Eint(1))), Den("Magazzino"))) env1;;

(* Dizionario vuoto: 0*)
eval (Fold(Fun("x", Sum(Den("x"), Eint(1))), Dictionary([]))) env1;;

(* Errore di tipo: non posso sommare booleani *)
eval (Iterate(Fun("x", Ifthenelse(Eq(Mod(Den("x"), Eint(2)), Eint(0)), Ebool(true), Ebool(false))), Den("Magazzino"))) env1;;
