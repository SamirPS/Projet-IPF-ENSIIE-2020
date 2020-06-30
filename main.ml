type tformula=
  | Value of bool
  | Var of string
  | Not of tformula
  | And of tformula * tformula
  | Or of tformula * tformula
  | Implies of tformula * tformula
  | Equivalent of tformula * tformula

type decTree=
  | DecLeaf of bool
  | DecRoot of string * decTree * decTree

type env = (string * bool) list 

type bddNode =
  |BddLeaf of int*bool
  |BddNode of int*string*int*int

type bdd = (int * (bddNode list))

let p1 = Var "P1";;
let p2 = Var "P2";;
let q1 = Var "Q1";;
let q2 = Var "Q2";;


let f1 = Equivalent(q1,q2);;
let f5 = And(Or(Not(q1),q2),Or(Not(q2),q1));;
let f2 = Equivalent(p1,p2);;
let ex1 = And(f1,f2);;

let f3= Equivalent(q2,q1);;
let f4 = Equivalent(p2,p1);;
let ex3= And(f2,f1);;
let ex2= Not(p1);;

 
(*  Permet d'eliminer les doublons dans a liste l 
    renvoie acc qui  est la liste l sans doublon    *)

let rec elimine (l: string list) (acc: string list) : (string list) = 
  match l with 
  |[] -> List.rev acc
  |t::q -> if (acc=[] || not(t=List.hd acc)) then elimine q (t::acc) else  elimine q acc ;;

(* Permet de chercher l'element var dans la liste ListVars
   et renvoie   le boolean associe a la var  *)

let rec find (listVars:env) (var:string) : (bool) =
  match listVars with
  | []-> failwith "Variable pas trouve"
  | (v,b)::q -> if (v=var) then b else find q var ;;
 

let rec getVars (valeur:tformula) : (string list) = 

  elimine (List.sort compare (match valeur with
  | Value _ -> []
  | Var var -> [var]
  | Not formula -> getVars formula
  | And (formula1,formula2) -> (getVars formula1)@(getVars formula2)
  | Or (formula1,formula2) -> (getVars formula1)@(getVars formula2)
  | Implies (formula1,formula2) -> (getVars formula1)@(getVars formula2)
  | Equivalent (formula1,formula2) -> (getVars formula1)@(getVars formula2) )) [] ;;
  


let rec evalFormula (listvar:env) (formula :tformula): (bool)=
    match formula with 
    | Value value -> value
    | Var var -> find listvar var
    | Not formula -> not(evalFormula listvar formula)
    | And (formula1,formula2) -> evalFormula listvar formula1 && evalFormula listvar formula2
    | Or (formula1,formula2) -> evalFormula listvar formula1 || evalFormula listvar formula2
    | Implies (formula1,formula2) -> not (evalFormula listvar formula1) ||  (evalFormula listvar formula2)
    | Equivalent (formula1,formula2) ->((evalFormula listvar formula1) && (evalFormula listvar formula2)) || (not(evalFormula listvar formula1) && not(evalFormula listvar formula2));;

let rec creation (listevar:string list) (envi:env) (formule:tformula): (decTree)  =
  match listevar with 
  | [] -> DecLeaf(evalFormula envi formule) 
  | t::q ->DecRoot(t,
                    creation q ((t,false)::envi) formule,
                    creation q ((t,true)::envi) formule);;
  
let rec buildDecTree (formule:tformula) : (decTree) =

  creation (getVars formule) [] formule;;
(* a' option soit  rien ou un objet *)

(* Question 4 *)

let rec indexNode (varname:string) (numg:int) (numd:int) ((index,listenoeud) : bdd) : (int option ) = 
  match listenoeud with 
  | [] -> None
  | BddNode(numero,t,numerog,numerod)::q ->  if (numerog=numg && numd=numerod && varname=t) then Some(numero) else indexNode varname numg numd (index,q)
  | BddLeaf(_,_)::q -> indexNode varname numg numd ((index,q) ) ;;

let rec indexLeaf (booleann:bool) ((index,listenoeud) : bdd) : (int option ) = 
  match listenoeud with 
  | [] -> None
  | BddNode(_,_,_,_)::q -> indexLeaf booleann  (index,q)
  | BddLeaf(numero,booleanval)::q -> if (booleanval=booleann) then Some(numero) else indexLeaf booleann ((index,q))  ;;

  let rec buildBddAux (formula : tformula) (vars: string list) (env: env) ( (index,lnoeud) as mybdd : bdd) : (int * bdd) =  
    
    match vars with 
  
      | [] -> (match indexLeaf (evalFormula env formula)  mybdd with
              |Some(numero) -> (numero,mybdd) 
              |None -> let newindex=index+1 in (newindex,(newindex,BddLeaf(newindex,evalFormula env formula)::lnoeud)) 
              )
    
      | var::suite->  let (i1, (index1,noeudg2)) = buildBddAux formula suite ((var,false)::env) mybdd in
                      let (i2, (index2,noeudg3)) = buildBddAux formula suite ((var,true)::env)  (index1,noeudg2) in
                      
                      match indexNode var i1 i2 (index1,noeudg2) with
                              |Some(numero) -> (numero,(index2,noeudg3)) 
                              |None -> let a=index2+1 in (a,(a,BddNode(a,var,i1,i2)::noeudg3 )) ;;
                
                              
  let buildBdd ( formule : tformula) : (bdd) =
      let (indexd,(index,node))= buildBddAux formule (getVars formule ) [] (0,[]) in
      (index,node);;

  let rec print_list ((index,liste):bdd) =
  match liste with 
  | [] ->  Printf.printf ("\n index = %d \n") (index)
  | BddLeaf(num,boliste)::l -> Printf.printf(" BddLeaf(%d,%B) ") num boliste; print_list ((index,l))
  | BddNode(num,nom,numg,numd)::l -> Printf.printf(" BddNode(%d,%s,%d,%d) ") num nom numg numd ; print_list ((index,l))  ;; 

 

(* Question 5 *)

let rec modif (node:bddNode list) (n:int) (p:int) (acc:bddNode list) : (bddNode list) =
  match node with 
  |[] -> acc
  |BddNode(num,var,numg,numd)::q when numg=n-> modif q n p (BddNode(num,var,p,numd)::acc)
  |BddNode(num,var,numg,numd)::q when numd=n-> modif q n p (BddNode(num,var,numg,p)::acc)
  |BddNode(num,var,numg,numd)::q -> modif q n p (BddNode(num,var,numg,numd)::acc)
  |BddLeaf (num,boolean)::q-> modif q n p (BddLeaf (num,boolean)::acc)

let rec simplifyBDDaux ((index,noeud):bdd) (aux:bddNode list): (bdd) =
  match noeud with 
  | [] -> (index,aux)
  | BddNode (num,var,numg,numd) as noeud ::q -> if(numg=numd) then simplifyBDDaux ((index,q)) (modif aux num numg []) else simplifyBDDaux ((index,q)) (noeud::aux)
  | BddLeaf (num,boolean) as leaf ::q  -> simplifyBDDaux ((index,q)) (leaf::aux);;

let simplifyBDD (mybdd:bdd) : (bdd) =
  simplifyBDDaux mybdd [];;



let isTautology (formule:tformula) : (bool) =
  let (index,noeud)= simplifyBDD (buildBdd formule ) in 
  match noeud with 
  |[BddLeaf(_,true)] -> true
  | _ -> false ;;

let rec comparenode (n1:bddNode list ) (n2:bddNode list ) : (bool) =
  match (n1,n2) with 
         |[],[]-> true
         |BddNode(a,b,c,d)::q,BddNode(e,f,g,h)::r-> if (a=e && b=f && c=g && d=h) then comparenode q r else false  
         |BddLeaf(a,b)::q,BddLeaf(c,d)::r -> if (a=c && b=d) then comparenode q r else false 
         |_,_-> false ;;
         
let areEquivalent (formule1:tformula) (formule2:tformula) : (bool) =
  let (i1,n1) =  simplifyBDD (buildBdd formule1) in 
  let (i2,n2) =  simplifyBDD (buildBdd formule2) in 
  
  comparenode n1 n2 ;;



let rec dotBDDaux (noeud:bddNode list) (monstr:string) =
  match noeud with 
  |[] -> monstr;
  |BddLeaf(a,b)::q -> dotBDDaux q ((string_of_int a) ^ " [style =bold,label=\"" ^ (string_of_bool b) ^"\"];\n"^monstr)
  |BddNode(a,b,c,d)::q->dotBDDaux q (monstr^(string_of_int a) ^ " [label=\""^b^"\"];\n"^(string_of_int a) ^ " -> "^(string_of_int c)^" [color=red,style=dashed];\n"^(string_of_int a)^" -> "^(string_of_int d)^";\n");;
                        
let dotBDD (name:string) ((index,noeud):bdd) =
  let fic2 = open_out (name^".dot") in
  let mystrfinal="digraph G { \n"^(dotBDDaux noeud "")^"}" in

  output_string fic2 mystrfinal;
  close_out fic2;;


let rec taille (arbre:decTree) : (int) =
  match arbre with 
  |DecLeaf _ ->1
  |DecRoot(_,g,d) -> 1 + taille g + taille d;;

let makestr index nom numg numd =
  let a=string_of_int index in
  a ^ " [ label =\" " ^ nom ^ " \"];\n "
  ^ a ^ " -> " ^( string_of_int numd )
  ^ " [ color = red , style = dashed ];\n "
  ^ a ^ " -> " ^( string_of_int (numd+numg) );;

let streleaf index p =
  (string_of_int index )
  ^ " [ style = bold , label =\" "
  ^ ( string_of_bool p ) ^ " \"];\n ";;
  
let rec dotDECaux arbre index =
  match arbre with
  | DecLeaf(p) -> streleaf index p
  | DecRoot(nom,DecLeaf(p),DecLeaf (q)) -> let numd=index+1 in
  (makestr index nom 1 numd) ^ " ;\n "
  ^ streleaf numd p
  ^ streleaf (numd+1) q 

  | DecRoot(nom,DecRoot(nomg,rootg,rootd),DecRoot(nomd,rootg1,rootd1)) -> let numd=index+1 in let numg=taille(DecRoot(nomg,rootg,rootd)) in 
  (makestr index nom numg numd)^ " ;\n "
  ^ dotDECaux ( DecRoot (nomg , rootg , rootd )  ) numd
  ^ dotDECaux (DecRoot (nomd , rootg1 , rootd1) ) (numd+numg)
  
  | _ -> "" ;;

let dotDEC arbre name =
  let fic2 = open_out (name^".dot") in
  let mystrfinal="digraph G { \n"^(dotDECaux arbre 0)^"}" in

  output_string fic2 mystrfinal;
  close_out fic2;;
  
  let a= dotBDD "bdd" (buildBdd  ex1);;   
  let b= dotDEC (buildDecTree ex1) "monbeautest";;
  
let test = 
  (*certaines Equivalcne de base *)
  assert(areEquivalent (Not(Not(p1))) p1 = true);
  assert(areEquivalent (Not(And(p1, p2))) (Or(Not(p1), Not(p2))) = true);
  assert(areEquivalent (Not(Or(p1, p2))) (And(Not(p1), Not(p2))) = true);
  assert(areEquivalent (Or(p1, p2)) (Or(p2,p1)) = true);
  assert(areEquivalent (And(p1, p2)) (And(p2,p1)) = true);
  assert(areEquivalent (And(p1,Or(p2,q1))) (Or(And(p1,p2), And(p1,q1))) = true);
  assert(areEquivalent (Or(p1,And(p2,q1))) (And(Or(p1,p2), Or(p1,q1))) = true);

  print_list  (simplifyBDDaux (buildBdd ex1) []);
  print_list   (buildBdd ex1)  ;
  assert(areEquivalent (Implies(p1, p2)) (Or(Not(p1), p2)) = true);
  assert(areEquivalent f1 f5= true);
  assert(areEquivalent ex1 ex2 = false);
  assert(areEquivalent ex2 ex2 = true);
  assert(areEquivalent (Value(true)) (Value(false)) = false);
  assert(areEquivalent (Equivalent(p1,q1)) (Equivalent(Not(p1),Not(q1))) = true);
  assert(getVars ex1 = ["P1";"P2"; "Q1"; "Q2"]);
  assert(evalFormula ["P1",false] ex2=true);
  assert(evalFormula ["P1",false;"P2",false;"Q1",false;"Q2",false] ex1=true);
  assert(buildDecTree ex1=DecRoot("P1",DecRoot ("P2",DecRoot("Q1",DecRoot ("Q2",DecLeaf true ,DecLeaf false ) ,
  DecRoot ("Q2" , DecLeaf false , DecLeaf true )) ,
  DecRoot ("Q1" , DecRoot ("Q2" , DecLeaf false , DecLeaf false ) ,
  DecRoot ("Q2" , DecLeaf false , DecLeaf false ))) ,
  DecRoot ("P2" ,
  DecRoot ("Q1" , DecRoot ("Q2" , DecLeaf false , DecLeaf false ) ,
  DecRoot ("Q2" , DecLeaf false , DecLeaf false )) ,
  DecRoot ("Q1" , DecRoot ("Q2" , DecLeaf true , DecLeaf false ) ,
  DecRoot ("Q2" , DecLeaf false , DecLeaf true )))));; 