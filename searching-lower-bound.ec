(* lower-bound proof framework and application to generalized or
   function *)

prover quorum=2 ["Z3" "Alt-Ergo"].

require import AllCore List FSet.

(* Auxiliary Lemmas *)

lemma fcardUindep1 (xs : 'a fset, x : 'a) :
  ! x \in xs => card (xs `|` fset1 x) = card xs + 1.
proof.
move => x_notin_xs.
by rewrite fcardUI_indep 1:fsetI1 1:x_notin_xs // fcard1.
qed.

lemma all_elemsP (f : 'a -> bool, xs : 'a fset) :
  all f (elems xs) <=> (forall (x : 'a), x \in xs => f x).
proof.
rewrite allP.
split => [H x x_in_xs | H x x_in_elems_xs].
by rewrite H -memE.
by rewrite H memE.
qed.

lemma all_elems_or (f : 'a -> bool, xs ys : 'a fset) :
  all f (elems (xs `|` ys)) <=> (all f (elems xs) /\ all f (elems ys)).
proof.
rewrite !all_elemsP.
split => [H | [#] H1 H2].
split => [z z_in_xs | z z_in_ys].
rewrite H in_fsetU; by left.
rewrite H in_fsetU; by right.
move => z; rewrite in_fsetU => [[z_in_xs | z_in_ys]].
by rewrite H1.
by rewrite H2.
qed.

(* theory of finite set ranges *)

theory FRange.

(* frange n is {i | 0 <= i < n} *)

op frange (n : int) : int fset = oflist (range 0 n).

(* let's prove this definition is good: *)

lemma frange_impl_range (n i : int) :
  i \in frange n => 0 <= i < n.
proof.
by rewrite mem_oflist mem_range.
qed.

lemma range_impl_frange (n i : int) :
  0 <= i < n => i \in frange n.
proof.
by rewrite mem_oflist mem_range.
qed.

lemma frange_iff_range (n i : int) :
  i \in frange n <=> 0 <= i < n.
proof.
split; [apply frange_impl_range | apply range_impl_frange].
qed.

lemma frange0 :
  frange 0 = fset0.
proof.
by rewrite /frange range_geq // -set0E.
qed.

lemma frangeS (n : int) :
  0 <= n => frange (n + 1) = frange n `|` fset1 n.
proof.
move => ge0_n.
rewrite fsetP => i.
rewrite in_fsetU1 2!mem_oflist 2!mem_range.
split => [[#] ge0_i i_lt_n_plus1 | [[#] ge0_i lt_i_n | ->]].
rewrite ltzS lez_eqVlt in i_lt_n_plus1.
elim i_lt_n_plus1 => [// | i_lt_n]; by left.
split => [// | _]; rewrite ltzS lez_eqVlt; by right.
split => [// |]; by rewrite ltzS lezz.
qed.

lemma card_frange (n : int) :
  0 <= n => card (frange n) = n.
proof.
elim n => [| i ge0_i IH].
by rewrite frange0 fcards0.
rewrite frangeS // fcardUindep1.
case (i \in frange i) => [| //].
by rewrite frange_iff_range.
by rewrite IH.
qed.

lemma sub_range_card_leq (xs : int fset, n : int) :
  0 <= n =>
  (forall (j : int), j \in xs => 0 <= j < n) =>
  card xs <= n.
proof.
move => ge0_n xs_sub_range.
rewrite -card_frange // subset_leq_fcard => i i_in_xs.
by rewrite range_impl_frange xs_sub_range.
qed.

lemma all_range_card_geq (xs : int fset, n : int) :
  0 <= n =>
  (forall (j : int), 0 <= j < n => j \in xs) =>
  n <= card xs.
proof.
move => ge0_n sub_xs.
rewrite -card_frange //.
rewrite subset_leq_fcard => i i_in_frange.
by rewrite sub_xs frange_impl_range.
qed.

lemma sub_range_card_max (xs : int fset, n : int) :
  card xs = n =>
  (forall (j : int), j \in xs => 0 <= j < n) =>
  (forall (j : int), 0 <= j < n => j \in xs).
proof.
move => <<- xs_sub_range j zero_le_j_lt_card_xs.
have -> : xs = frange (card xs).
  rewrite eqEcard.
  split => [i i_in_xs |].
  by rewrite range_impl_frange xs_sub_range.
  rewrite card_frange 1:fcard_ge0 lezz.
by rewrite range_impl_frange.
qed.

end FRange.

(* theory for generating all lists of a given length whose
   elements come from a given list *)

theory AllLists.


lemma all_flatten (f : int -> bool, xss : int list list) :
  all f (flatten xss) = all (all f) xss.
proof.
elim xss => [| x xss IH /=].
by rewrite flatten_nil.
by rewrite flatten_cons all_cat IH.
qed.


print sort.
op xs = [1; 5; 3; 2].
op compare (x : int, y : int) : bool = x <= y.

op x = 2.
op y = 3.
lemma com_ex: (compare x y) = true.
proof.
smt().
qed.

op e: int -> int -> bool = compare.
print sort.
lemma sort_ex: sort e xs = [1; 2; 3; 5].
proof.
smt().
qed.

print map.


op next (xs : int list, yss : int list list) : int list list =
  flatten
  (map
   (fun x =>
      map (fun ys => x :: (sort e ys)) yss)
   xs).

lemma next (xs : int list, yss : int list list) :
  next xs yss =
  flatten
  (map
   (fun x =>
      map (fun ys => x ::(sort e ys)) yss)
   xs).
 proof.
 
by rewrite /next.
qed.


op all_lists (xs : int list, n : int) = fold (next xs) [[]] n.

lemma all_lists0 (xs : int list) :
  all_lists xs 0 = [[]].
proof.
by rewrite /all_lists fold0.
qed.

lemma all_listsS (xs : int list, n : int) :
  0 <= n =>
  all_lists xs (n + 1) = next xs (all_lists xs n).
proof.
move => ge0_n.
rewrite /all_lists foldS.
  trivial.
  trivial.
qed.

lemma all_listsS_iff (xs ys : int list, n : int) :
  0 <= n =>
  ys \in all_lists xs (n + 1) <=>
  exists (z : int, zs : int list),
  ys = z :: zs /\ z \in xs /\ zs \in all_lists xs n /\ z <= (nth witness zs 1).
proof.
move => ge0_n.
rewrite all_listsS // next /= -flatten_mapP.
split => [[z] [#] /= |].
rewrite mapP => z_in_xs [zs] [#] => zs_in_all_n ->>.
  admit.
(*
by exists z zs.
move => [z zs] [#] -> z_in_xs zs_in_all_n.
exists z.
by rewrite z_in_xs /= (map_f ((::) z)).
  *)
  admit.
qed.

lemma all_lists_arity_wanted (xs : int list, n : int) :
  0 <= n =>
  all
  (fun ys => size ys = n /\ all (mem  xs) (sort e ys))
  (all_lists xs n).
proof.
elim n => [| i ge0_i IH].
  admit.
  admit.

(*
  by rewrite all_lists0.
rewrite allP in IH.
rewrite allP => zs.
rewrite all_listsS_iff //.
move => [w ws] [#] -> w_in_xs ws_in_all_i /=.
  rewrite w_in_xs /=. 
have /= [#] <- -> /= := (IH ws ws_in_all_i).
by rewrite addzC.
*)
qed.

lemma all_lists_arity_have (xs ys : int list, n : int) :
  0 <= n => size ys = n => (all (mem (sort e xs)) ys) =>
  ys \in all_lists xs n.
proof.
move : n.
elim ys => [n ge0_n /= <- | y ys IH n ge0_n].
by rewrite all_lists0.
rewrite /= => <- [#] y_in_xs all_mem_xs_ys.
rewrite addzC all_listsS_iff 1:size_ge0.
exists y ys => /=.
  admit.

(*
by rewrite y_in_xs /= IH 1:size_ge0.
*)
qed.

lemma size_nseq_norm (n : int, x : int) :
  0 <= n => size (nseq n x) = n.
proof.
rewrite lez_eqVlt => ge0_n.
rewrite size_nseq /max.
by elim ge0_n => ->.
qed.

lemma all_lists_nseq (x : int, xs : int list, n : int) :
  0 <= n => x \in  (sort e xs) => nseq n x \in all_lists xs n.
proof.
move => ge0_n x_in_xs.
rewrite all_lists_arity_have //.
by rewrite size_nseq_norm.
rewrite allP => z; by rewrite mem_nseq => [#] _ => ->>.
qed.

(* makes a list of length n all of whose elements are either
   x1 or x2; when the elements index i is in zs, x1 is used;
   otherwise x2 is used *)

op all_lists_make (x1 x2 : int, f : int -> bool, n : int) =
  mkseq (fun i => if f i then x1 else x2) n.

lemma all_lists_make_size (x1 x2 : int, f : int -> bool, n : int) :
  0 <= n => size (all_lists_make x1 x2 f n) = n.
proof.
rewrite lez_eqVlt => ge0_n.
rewrite /all_lists_make size_mkseq /max.
by elim ge0_n => ->.
qed.

lemma all_lists_make_all_in
      (xs : int list, x1 x2 : int, f : int -> bool, n : int) :
  0 <= n => x1 \in xs => x2 \in xs =>
  all (mem xs) (all_lists_make x1 x2 f n).
proof.
move => ge0_n x1_in_xs x2_in_xs.
rewrite /all_lists_make allP => z.
rewrite mkseqP => [] [i] [#] ge0_i i_rng -> /=.
by case (f i).
qed.

lemma all_lists_make_have (xs : int list, x1 x2 : int, f : int -> bool, n : int) :
  0 <= n => x1 \in (sort e xs) => x2 \in (sort e xs) =>
  (all_lists_make x1 x2 f n) \in all_lists xs n.
proof.
move => ge0_n x1_in_xs x2_in_xs.
by rewrite all_lists_arity_have // 1:all_lists_make_size //
           all_lists_make_all_in.
qed.

lemma all_lists_make_nth (x1 x2 : int, f : int -> bool, n, i : int) :
  0 <= n => 0 <= i < n =>
  nth witness (all_lists_make x1 x2 f n) i = if f i then x1 else x2.
proof.
move => ge0_n i_rng.
rewrite /all_lists_make.
by rewrite nth_mkseq.
qed.

end AllLists.

(* lower bounds theory *)

theory LB.

(* theory parameters *)

type inp = int.  (* type of inputs *)

op univ : inp list.  (* universe with concrete ordering *)

op def : inp.  (* default inp *)

axiom univ_def : mem univ def.  (* default inp is in univ *)

axiom univ_uniq : uniq univ.  (* no duplicates in univ *)

type out.  (* type of outputs *)

op arity : {int | 0 <= arity} as ge0_arity.  (* arity of f *)

(* list given to f should have size arity, and all elements should
   be in univ *)

 op f : inp -> inp list -> out option.

(* op f : inp list -> out option. *)

  (* when argument to f is good, we get Some of an answer *)

(*

op sorted(inps : inp list) : bool =
  forall (i : int, j : int),
((0 <= i < arity) /\ (0 <= j < arity) /\ (i <= j) => ((nth witness inps i) <= (nth witness inps j))) => true.

op not_sorted (inps: inp list) : bool =
exists (i : int, j : int),
((0 <= i < arity) /\ (0 <= j < arity) /\ (i <= j) => ((nth witness inps j) < (nth witness inps i))) => true.


op k_in_list_true (inps : inp list, k : inp) : bool =
  exists (i : int),
  (0 <= i < arity /\ nth witness inps i = k) => true.

axiom good (xs : inp list, k : inp) : (* additional constraint is that all lists need to be sorted and the element that is being searched for should be in the list *)
  (size xs = arity /\ sorted xs /\ k_in_list_true xs k) => all (mem univ) xs =>
  exists (y : out), f xs = Some y.

(* when argument to f is bad, we get None *)

axiom bad (xs : inp list, k : inp) : (* Check if the !all clause is needed for the axiom bad*)
  size xs <> arity \/ not_sorted xs \/ !(k_in_list_true xs k) \/ !(all (mem univ) xs) =>
  f xs = None.
  *)


op k_in_list_true (inps : inp list, k : inp) : bool =
  exists (i : int),
  (0 <= i < arity /\ nth witness inps i = k) => true.

axiom good (xs : inp list, k : inp) : (* additional constraint is that all lists need to be sorted and the element that is being searched for should be in the list *)
  (size xs = arity /\ sorted AllLists.e xs /\ k_in_list_true xs k) => all (mem univ) xs =>
  exists (y : out), f k xs = Some y.

(* when argument to f is bad, we get None *)

axiom bad (xs : inp list, k : inp) : (* Check if the !all clause is needed for the axiom bad*)
  size xs <> arity \/ !(sorted AllLists.e xs) \/ !(k_in_list_true xs k) \/ !(all (mem univ) xs) =>
f k xs = None.




  (* end of theory parameters *)

(* all possible lists of inputs of length arity, i.e., all
   possible good inputs to f *)

op init_inpss : inp list list = AllLists.all_lists univ arity.

(* all lists of possible inputs must cause f to return non-None
   answers *)

print map.

op inpss_invar (inpss : inp list list, k : inp) : bool =
  all is_some (map (f k) inpss).


lemma inpss_invar_init (k : inp) : (* fails at smt. Invalid allists theory. Check if axiom good is good? *)
  inpss_invar init_inpss k.
proof.
rewrite /inpss_invar /init_inpss.
have H := AllLists.all_lists_arity_wanted univ arity _.
  apply ge0_arity.
admit.

(* 
smt(allP mapP good).
  *)

qed.

lemma inpss_invar_filter (inpss : inp list list, g : inp list -> bool, k: inp) :
  inpss_invar inpss k => (inpss_invar (filter g inpss) k).
proof.
rewrite /inpss_invar.
smt(mapP mem_filter allP map_f).
qed.

lemma inpss_invar_size (inpss : inp list list, k: inp) : (* axiom good/ alllists *)
  inpss_invar inpss k =>
  all (fun inps => size inps = arity) inpss.
proof.
rewrite /inpss_invar => all_is_some_map_f_inpss.
rewrite allP => inps inps_in_inpss /=.
rewrite allP in all_is_some_map_f_inpss.
  have H := all_is_some_map_f_inpss (f k inps) _.
print map_f.
smt(map_f).
smt(good bad).

qed.

lemma inpss_invar_size_alt (inpss : inp list list, inps : inp list, k: inp) :
  inpss_invar inpss k => inps \in inpss =>
  size inps = arity.
proof.
move => inv.
have := inpss_invar_size inpss k _.
  done.
rewrite allP /= => all_of_inpss_size inps_in_inpss.
by apply all_of_inpss_size.
qed.

(* the game is done when f agrees on all possible input lists
   (filtering will never remove all elements) *)

op inpss_done (inpss : inp list list, k : inp) : bool =
  forall (x y : out option),
  x \in map (f k) inpss  => y \in map (f k) inpss => x = y.

(* an algorithm *)

module type ALG = {
  (* tell algorithm to initialize itself *)
  proc init(k : int) : unit

  (* ask algorithm to make an input query, choosing an input index i
     such that 0 <= i < arity *)
  proc make_query() : int

  (* tell algorithm the result of its query *)
  proc query_result(x : inp) : unit
}.

(* an adversary *)

module type ADV = {
  (* tell adversary to initialize itself *)
  proc init() : inp

  (* ask adversary to answer query of what the ith input is *)
  proc ans_query(i : int) : inp
}.

(* game connecting algorithm and adversary *)

module G(Alg : ALG, Adv : ADV) = {
  proc main() : bool * int = {
    var inpss : inp list list;  (* current possible lists of inputs *)
    var don : bool;  (* is game done? *)
    var error : bool;  (* has game made illegal query? *)
    var stage : int;  (* stage of game *)
    var queries : int fset;  (* valid queries made by algorithm *)

    var i : int;
  var inp : inp;
    var k : inp;

    k <@ Adv.init();
    Alg.init(k);
    inpss <- init_inpss;  (* start with all lists of inputs *)
    (* by lemma inpss_invar_init, the invariant is established *)
    error <- false;  (* no error so far *)
    don <- inpss_done inpss k;  (* are we already done? *)
    stage <- 0;
    queries <- fset0;
    while (!don /\ !error) {
      i <@ Alg.make_query();  (* let Alg make query *)
      if (0 <= i < arity /\ ! i \in queries) {
        queries <- queries `|` fset1 i;
        stage <- stage + 1;
        inp <@ Adv.ans_query(i);  (* ask Adv to answer query *)
        inp <- mem univ inp ? inp : def;  (* use def if inp not in universe *)
        Alg.query_result(inp);  (* tell Alg result of its query *)
        (* get rid of lists of inputs that aren't consistent with answer *)
        inpss <- filter (fun inps => nth witness inps i = inp) inpss;
        don <- inpss_done inpss k;  (* perhaps we're done now? *)
      }
      else {
        error <- true;  (* query was invalid *)
      }
    }
    return (error, stage);
  }
}.

pred queries_in_range (queries : int fset) =
  forall (i : int), i \in queries => 0 <= i < arity.

lemma queries_in_range0 :
  queries_in_range fset0.
proof.
move => i.
by rewrite in_fset0.
qed.

lemma queries_in_range_add (queries : int fset, i : int) :
  0 <= i < arity => queries_in_range queries =>
  queries_in_range (queries `|` fset1 i).
proof.
move => i_in_rng @/queries_in_range qir_queries j.
rewrite in_fsetU1 => [] [j_in_queries | -> //].
by apply qir_queries.
qed.

lemma queries_in_range_card_le_arity (queries : int fset) :
  queries_in_range queries => card queries <= arity.
proof.
move => qir_queries.
rewrite FRange.sub_range_card_leq 1:ge0_arity.
apply qir_queries.
qed.

pred all_in_range_queries (queries : int fset) =
  forall (i : int), 0 <= i < arity => i \in queries.

lemma all_queries_cond (queries : int fset) :
  queries_in_range queries =>
  (card queries = arity <=> all_in_range_queries queries).
proof.
move => qir_queries.
split => [card_queries_eq_arity i i_in_rng | airq_queries].
by rewrite (FRange.sub_range_card_max queries arity).
rewrite (lez_anti (card queries) arity) //.
split => [| _].
by rewrite (FRange.sub_range_card_leq queries arity) 1:ge0_arity.
by rewrite (FRange.all_range_card_geq queries arity) 1:ge0_arity.
qed.

pred queries_eq_all_range (queries : int fset) =
  queries_in_range queries /\ all_in_range_queries queries.

lemma all_queries_predP (queries : int fset, f : int -> bool) :
  queries_eq_all_range queries =>
  (all f (elems queries)) <=> (forall (i : int), 0 <= i < arity => f i).
proof.
move => @/queries_eq_all_range [#] qir_queries airq_queries.
split.
rewrite all_elemsP => all_queries_f i i_in_rng.
by rewrite all_queries_f airq_queries.
rewrite all_elemsP => H x x_in_queries.
by rewrite H qir_queries.
qed.

lemma G_ll (Alg <: ALG) (Adv <: ADV{Alg}) :
  islossless Alg.init => islossless Alg.make_query =>
  islossless Alg.query_result =>
  islossless Adv.init => islossless Adv.ans_query =>
  islossless G(Alg, Adv).main.
proof.
move =>
  Alg_init_ll Alg_make_query_ll Alg_query_result_ll
  Adv_init_ll Adv_ans_query_ll.
proc.
while
  (queries_in_range queries /\ stage = card queries)
  (if error then 0 else arity - stage + 1).
move => z.
seq 1 :
  (queries_in_range queries /\ stage = card queries /\ !don /\ !error /\
  (if error then 0 else arity - stage + 1) = z).
auto.
call (_ : true).
auto.
if.
wp.
call (_ : true).
wp.
call (_ : true).
auto; progress.
by rewrite queries_in_range_add.
by rewrite fcardUindep1.
smt().
auto; progress; smt(queries_in_range_card_le_arity).
hoare.
call (_ : true).
auto.
smt().
wp.
call (_ : true).
call (_ : true).
auto; progress.
rewrite queries_in_range0.
by rewrite fcards0.
smt(queries_in_range_card_le_arity).
qed.

end LB.

(* application to search function - changes to be made ... :( *)

type inp = int.

op univ = [0; 1; 2].

type out = int.

(* arity can be any non-negative number *)

op arity : {int | 0 <= arity} as ge0_arity.

(* these two operators assume argument has size arity *)

op all_false (inps : int list, k: inp) =
  forall (i : int),
  0 <= i < arity => nth witness inps i <> k.

op k_true (inps : int list, k: inp)=
  exists (i : int),
  0<= i < arity /\ nth witness inps i = k => forall (j: int), 0<=j<i => nth witness inps j <> k.


(* What is the correct op for k_false???????????????????? *)
op k_false (inps : int list, k: inp)=
  forall (i : int),
  0<= i < arity /\ nth witness inps i = k => exists (j: int), 0<=j<i => nth witness inps j = k.


(*
op some_true (inps : bool list) =
  exists (i : int),
  0 <= i < arity /\ nth witness inps i = true.
  *)


lemma some_true_equiv (inps : int list, k: inp) :
  k_true inps k <=> ! (k_false inps k).
proof.
  rewrite /k_true /k_false negb_forall /=.
  split.
  search [!]. 

split => [[] i [] i_rng nth_i_true | [] i].
exists i.
by rewrite negb_imply neqF /= i_rng nth_i_true.
rewrite negb_imply neqF /= => [[]] x_rng nth_i.
exists i; by rewrite x_rng nth_i.
qed.

lemma all_false_equiv (inps : bool list) :
  all_false inps <=> ! (some_true inps).
proof.
rewrite /some_true /all_false negb_exists /=.
split => [H i | H i i_rng].
rewrite negb_and.
case (0 <= i < arity) => [i_arity | //].
right; by rewrite -neqF H.
have /negb_and [] // := H i.
by rewrite neqF eqT.
qed.

lemma all_false_nseq :
  all_false (nseq arity false).
proof.
rewrite /all_false => i i_rng.
by rewrite nth_nseq.
qed.

(* generalized or function *)

op f (xs : inp list) =
  if size xs <> arity
  then None
  else Some(some_true xs).

lemma f_false (xs : inp list) :
  size xs = arity => all_false xs => f xs = Some false.
proof.
rewrite /f => -> /=.
by rewrite all_false_equiv neqF.
qed.

lemma f_false_nseq :
  f (nseq arity false) = Some false.
proof.
rewrite f_false // 1:AllLists.size_nseq_norm 1:ge0_arity // all_false_nseq.
qed.

lemma f_true (xs : inp list) :
  size xs = arity => some_true xs => f xs = Some true.
proof.
by rewrite /f => -> ->.
qed.

lemma all_mem_univ (xs : inp list) :
  all (mem univ) xs.
proof.
elim xs => [// | x ys IH].
rewrite /univ /=.
by case x.
qed.

clone import LB as LB' with
  type inp <- inp,
  op univ  <- univ,
  op def   <- true,
  type out <- out,
  op arity <- arity,
  op f     <- f
proof *.
realize ge0_arity. rewrite ge0_arity. qed.

realize univ_uniq. by rewrite /univ. qed.

realize univ_def. by rewrite /univ. qed.

realize good.
rewrite /f => xs -> _.
by exists (some_true xs).
qed.

realize bad.
rewrite /f.
move => xs [-> // |].
by have := all_mem_univ xs.
qed.

lemma nseq_false_in_init_inpss :
  nseq arity false \in init_inpss.
proof.
by rewrite /init_inpss AllLists.all_lists_nseq 1:ge0_arity.
qed.

(* here is our adversary *)

module Adv : ADV = {
  proc init() : unit = { }

  proc ans_query(i : int) : inp = {
    return false;
  }
}.

lemma Adv_ans_query_false :
  hoare[Adv.ans_query : true ==> !res].
proof.
proc; auto.
qed.

lemma Adv_init_ll : islossless Adv.init.
proof.
proc; auto.
qed.

lemma Adv_ans_query_ll : islossless Adv.ans_query.
proof.
proc; auto.
qed.

pred all_queries_false (queries : int fset, inps : inp list) =
  all (fun i => nth witness inps i = false) (elems queries).

lemma all_queries_falseP (queries : int fset, inps : inp list) :
  queries_in_range queries =>
  all_queries_false queries inps <=>
  forall (i : int),
  0 <= i < arity => i \in queries =>
  ! nth witness inps i.
proof.
move => qir_queries.
rewrite /all_queries_false allP.
split => [H i i_rng i_in_queries | H x].
have /= -> // := H i _.
by rewrite -memE.
rewrite -memE /= => x_in_queries.
by rewrite neqF H 1:qir_queries.
qed.

lemma all_queries_false_queries_eq_all_range (queries : int fset) :
  queries_eq_all_range queries =>
  all_queries_false queries = all_false.
proof.
rewrite /queries_eq_all_range => [#] qir_queries airq_queries.
apply fun_ext => i.
rewrite eq_iff.
rewrite /all_queries_false all_queries_predP //.
by split => [| ?].
qed.

lemma all_queries_false_nseq (queries : int fset) :
  queries_in_range queries =>
  all_queries_false queries (nseq arity false).
proof.
move => qir_queries.
rewrite /all_queries_false all_elemsP => x x_in_queries /=.
by rewrite nth_nseq 1:qir_queries.
qed.

lemma filter_all_queries_false0 :
  filter (all_queries_false fset0) init_inpss = init_inpss.
proof.
rewrite /all_queries_false /=.
have -> :
  (fun (inps : bool list) =>
   all (fun (i : int) => nth witness inps i = false) (elems fset0)) =
  predT.
  apply fun_ext => inps.
  by rewrite elems_fset0.
by rewrite filter_predT.
qed.

lemma filter_all_queries_false_add (queries : int fset, i : int) :
  filter (all_queries_false (queries `|` fset1 i)) init_inpss =
  filter
  (fun inps => nth witness inps i = false)
  (filter (all_queries_false queries) init_inpss).
proof.
rewrite -filter_predI /predI.
congr.
apply fun_ext => bs.
by rewrite /all_queries_false all_elems_or elems_fset1 andbC.
qed.

lemma filter_all_queries_false_f_false (queries : int fset) :
  queries_in_range queries =>
  exists (xs : inp list),
  (xs \in filter (all_queries_false queries) init_inpss) /\ f xs = Some false.
proof.
move => qir_queries.
exists (nseq arity false).
split.
rewrite mem_filter.
split.
by rewrite all_queries_false_nseq.
rewrite nseq_false_in_init_inpss.
apply f_false_nseq.
qed.

lemma f_true_all_lists_make (queries : int fset, i : int) :
  0 <= i < arity => ! (i \in queries) =>
  f (AllLists.all_lists_make false true (fun i => i \in queries) arity) =
  Some true.
proof.
move => i_rng i_notin_queries.
rewrite f_true 1:AllLists.all_lists_make_size 1:ge0_arity //
        /some_true.
exists i.
split => [// |].
by rewrite AllLists.all_lists_make_nth // 1:ge0_arity /=
          i_notin_queries.
qed.

lemma filter_all_queries_false_f_true (queries : int fset, i : int) :
  queries_in_range queries => 0 <= i < arity => ! (i \in queries) =>
  exists (xs : inp list),
  (xs \in filter (all_queries_false queries) init_inpss) /\ f xs = Some true.
proof.
move => qir_queries i_rng i_notin_queries.
exists (AllLists.all_lists_make false true (fun i => i \in queries) arity).
split.
rewrite mem_filter.
split.
rewrite all_queries_falseP // => j j_rng j_in_queries.
rewrite AllLists.all_lists_make_nth 1:ge0_arity 1:qir_queries //
           x_in_queries.
rewrite /init_inpss AllLists.all_lists_make_have 1:ge0_arity //.
by rewrite (f_true_all_lists_make _ i).
qed.

lemma filter_all_queries_false_done (queries : int fset) :
  queries_in_range queries =>
  (card queries = arity <=>
   inpss_done (filter (all_queries_false queries) init_inpss)).
proof.
move => qir_queries.
split => [cq_eq_arities | done_filtering].
rewrite all_queries_false_queries_eq_all_range.
rewrite all_queries_cond // in cq_eq_arities.
rewrite /inpss_done => out1 out2.
rewrite 2!mapP.
move => [xs] [#] xs_in_filter ->.
move => [ys] [#] ys_in_filter ->.
rewrite mem_filter in xs_in_filter.
rewrite mem_filter in ys_in_filter.
elim xs_in_filter => xs_af xs_in_init.
elim ys_in_filter => ys_af ys_in_init.
have size_xs : size xs = arity.
  rewrite (inpss_invar_size_alt init_inpss) 1:inpss_invar_init //.
have size_ys : size ys = arity.
  rewrite (inpss_invar_size_alt init_inpss) 1:inpss_invar_init //.
by rewrite f_false // f_false.
rewrite all_queries_cond // => i i_in_rng.
case (i \in queries) => [// | i_notin_queries].
rewrite /inpss_done in done_filtering.
have [] xs [#] xs_in_fil f_xs_false :
  exists (xs : inp list),
  xs \in filter (all_queries_false queries) init_inpss /\
  f xs = Some false.
  by rewrite filter_all_queries_false_f_false.
have [] ys [#] ys_in_fil f_ys_true :
  exists (ys : inp list),
  ys \in filter (all_queries_false queries) init_inpss /\
  f ys = Some true.
  by rewrite (filter_all_queries_false_f_true _ i).
have : f xs = f ys.
  apply done_filtering; by rewrite map_f.
by rewrite f_xs_false f_ys_true.
qed.

lemma G_Adv_main (Alg <: ALG{Adv}) :
  hoare [G(Alg, Adv).main : true ==> res.`1 \/ res.`2 = arity].
proof.
proc.
seq 7 :
  (inpss = init_inpss /\ error = false /\ don = inpss_done inpss /\
   stage = 0 /\ queries = fset0).
wp.
call (_ : true); first auto.
call (_ : true); first auto.
while
  (stage = card queries /\ queries_in_range queries /\
   inpss = filter (all_queries_false queries) init_inpss /\
   don = inpss_done inpss).
seq 1 :
  (stage = card queries /\ queries_in_range queries /\
   inpss = filter (all_queries_false queries) init_inpss /\
   don = inpss_done inpss /\ !don /\ !error).
call (_ : true); first auto.
if.
wp.
call (_ : true); first auto.
call Adv_ans_query_false.
auto; progress.
by rewrite fcardUindep1.
smt(queries_in_range_add).
by rewrite filter_all_queries_false_add H5.
auto.
auto; progress.
by rewrite fcards0.
by rewrite queries_in_range0.
by rewrite filter_all_queries_false0.
smt(filter_all_queries_false_done).
qed.

lemma lower_bound_or &m :
  exists (Adv <: ADV),
  islossless Adv.init /\ islossless Adv.ans_query /\
  forall (Alg <: ALG{Adv}),
  islossless Alg.init => islossless Alg.make_query =>
  islossless Alg.query_result =>
  Pr[G(Alg, Adv).main() @ &m : res.`1 \/ res.`2 = arity] = 1%r.
proof.
exists Adv.
split; first apply Adv_init_ll.
split; first apply Adv_ans_query_ll.
move => Alg Alg_init_ll Alg_make_query_ll Alg_query_result_ll.
byphoare => //.
conseq
  (_ : true ==> true)
  (_ : true ==> res.`1 \/ res.`2 = arity) => //.
apply (G_Adv_main Alg).
rewrite (G_ll Alg Adv) 1:Alg_init_ll 1:Alg_make_query_ll
        1:Alg_query_result_ll 1:Adv_init_ll Adv_ans_query_ll.
qed.