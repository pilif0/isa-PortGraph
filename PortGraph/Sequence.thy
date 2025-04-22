theory Sequence
  imports
    PortGraph
    Util_Mapping
begin

section\<open>Port Graph Sequencing\<close>

subsection\<open>Sorting Theorems\<close>
(* General sorting theorems, extract *)

(* Sorting by a key means that the result is sorted with respect to ordering by that key *)
lemma sorted_wrt_sort_key:
  "sorted_wrt (\<lambda>x y. k x \<le> k y) (sort_key k xs)"
  using sorted_wrt_map by fastforce

lemma map_insort_key:
  fixes f :: "'a \<Rightarrow> 'b"
    and k :: "'a \<Rightarrow> ('k :: linorder)"
    and k' :: "'b \<Rightarrow> 'k"
  assumes "\<And>x y. \<lbrakk>x \<in> insert a (set xs); y \<in> insert a (set xs); k x \<le> k y\<rbrakk> \<Longrightarrow> k' (f x) \<le> k' (f y)"
  shows "map f (insort_key k a xs) = insort_key k' (f a) (map f xs) "
  using assms
  apply (induct xs)
   apply simp_all
  apply (clarsimp simp add: not_le)
  apply safe
  oops

(*
  Mapping a function over a list commutes with sorting it by some key if: the function is monotonic
  with respect to that key, the list has no duplicates, the key is injective on the mapped list, and
  the function is injective on the original list.
  (I have a feeling that these may not all be necessary - especially the distinctness.)
 *)
lemma map_sort_key:
  fixes k :: "'a \<Rightarrow> 'b :: linorder"
  assumes "\<And>x y. \<lbrakk>x \<in> set xs; y \<in> set xs; k x \<le> k y\<rbrakk> \<Longrightarrow> k (f x) \<le> k (f y)"
      and "distinct xs"
      and "inj_on k (set (map f xs))"
      and "inj_on f (set xs)"
    shows "map f (sort_key k xs) = sort_key k (map f xs)"
(*proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
    apply simp
    apply (subst Cons[symmetric])
    apply (rule map_insort_key)
    apply simp
    sorry
  oops*)
proof -
  have sorted_LHS:
    "sorted_wrt (\<lambda>x y. k x \<le> k y) (map f (sort_key k xs))"
    using assms sorted_wrt_sort_key sorted_wrt_map
    by (metis (mono_tags, lifting) set_sort sorted_wrt_mono_rel)

  note map_step =
    sorted_distinct_set_unique[
      OF  sorted_map[THEN iffD2, OF sorted_LHS]
          _
          sorted_map[THEN iffD2, OF sorted_wrt_sort_key[of k "map f xs"]]
    ]
  have "inj_on k (set (map f (sort_key k xs)) \<union> set (sort_key k (map f xs)))"
    using assms(3) by (simp add: inj_on_def)
  moreover have "distinct (map k (map f (sort_key k xs)))"
    using assms(2,3,4) by (simp add: distinct_map inj_on_def)
  moreover have "distinct (map k (sort_key k (map f xs)))"
    using assms(2,3,4) by (simp add: distinct_map inj_on_def)
  moreover have "set (map k (map f (sort_key k xs))) = set (map k (sort_key k (map f xs)))"
    by (simp add: image_image)
  ultimately show ?thesis
    using inj_on_map_eq_map iffD1 map_step by metis
qed

(*
  Sorting two lists by a key gives equal results if: they contain the same elements with no
  duplicates and the key is injective on those elements.
  (I have a feeling that these may not all be necessary - especially the distinctness.)
 *)
lemma sort_key_eqI:
  assumes "set xs = set ys"
      and "distinct xs"
      and "distinct ys"
      and "inj_on k (set xs)"
    shows "sort_key k xs = sort_key k ys"
  by (smt (verit, best) assms distinct_map distinct_sort inj_on_map_eq_map list.set_map set_sort sorted_distinct_set_unique sorted_sort_key sup.idem)

subsection\<open>Stitching Interface Edges\<close>

subsubsection\<open>Edges To Open Ports\<close>

(* Take list of edges, pick out those coming into open ports and group them by that port *)
primrec edgesByOpenTo :: "('s, 'a, 'p) edge list \<Rightarrow> (('s, 'a) port, ('s, 'a, 'p) edge list) mapping"
  where
    "edgesByOpenTo [] = Mapping.empty"
  | "edgesByOpenTo (e#es) =
    ( if place_open (edge_to e)
        then Mapping.map_default (place_port (edge_to e)) Nil (Cons e) (edgesByOpenTo es)
        else edgesByOpenTo es
    )"

lemma edgesByOpenTo_Some_preserve:
  assumes "\<exists>z. Mapping.lookup (edgesByOpenTo es) p = Some z"
  shows "\<exists>z. Mapping.lookup (edgesByOpenTo (e # es)) p = Some z"
  using assms by (metis edgesByOpenTo.simps(2) lookup_map_default lookup_map_default_neq)

lemma edgesByOpenTo_Some_ex:
  assumes "e \<in> set es"
      and "place_open (edge_to e)"
      and "place_port (edge_to e) = p"
    shows "\<exists>zs. Mapping.lookup (edgesByOpenTo es) p = Some zs"
  using assms
proof (induct es)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    using Cons
    by (cases "e = x")
       (simp_all add: lookup_map_default lookup_map_default')
qed

lemma edgesByOpenTo_in_result:
  assumes "e \<in> set es"
      and "Mapping.lookup (edgesByOpenTo es) p = Some zs"
      and "place_open (edge_to e)"
      and "place_port (edge_to e) = p"
    shows "e \<in> set zs"
  using assms
proof (induct es arbitrary: zs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases "e = x")
    case True
    then show ?thesis
      using Cons by (fastforce simp add: lookup_map_default)
  next
    case e: False

    show ?thesis
    proof (cases "edge_to x")
      case (GroundPort qp)
      then show ?thesis
        using Cons e by simp
    next
      case (OpenPort p')
      then show ?thesis
      proof (cases "p' = p")
        case True
        then show ?thesis
          using Cons e OpenPort
          by (simp add: lookup_map_default lookup_default_def)
             (metis edgesByOpenTo_Some_ex list.set_intros(2) option.simps(5))
      next
        case False
        then show ?thesis
          using Cons e OpenPort by (simp add: lookup_map_default_neq)
      qed
    qed
  qed
qed

lemma edgesByOpenTo_Some:
  assumes "Mapping.lookup (edgesByOpenTo es) p = Some xs"
  shows "xs = filter (\<lambda>x. edge_to x = OpenPort p) es"
  using assms
proof (induct es arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case
  proof (cases "edge_to a = OpenPort p")
    case True
    then show ?thesis
    proof (cases "Mapping.lookup (edgesByOpenTo as) p")
      case None
      then show ?thesis
        using Cons True edgesByOpenTo_Some_ex empty_filter_conv
        by (fastforce simp add: lookup_map_default lookup_default_def)
    next
      case (Some zs)
      then show ?thesis
        using Cons True by (simp add: lookup_map_default lookup_default_def)
    qed
  next
    case False
    then show ?thesis
      using Cons by (cases "edge_to a") (simp_all add: lookup_map_default_neq)
  qed
qed

text\<open>Edge from one of the collected edge lists must come from the input\<close>
lemma edgesByOpenTo_in_values: (* TODO unused *)
  assumes "e \<in> set es"
    and "es \<in> snd ` Mapping.entries (edgesByOpenTo xs)"
    shows "e \<in> set xs"
  using assms
  apply -
  apply (induct xs arbitrary: e es)
  apply simp
  apply (case_tac "place_open (edge_to a)" ; simp add: )
  apply clarsimp
  apply (subst (asm) entries_map_default)
  apply (case_tac "Mapping.lookup (edgesByOpenTo xs) (place_port (edge_to a)) = None")
  using image_iff apply fastforce
  apply clarsimp
  by (metis image_eqI in_entriesI set_ConsD snd_conv)

lemma edgesByOpenTo_qualify:
  "Mapping.map_values (\<lambda>k. map (qualifyEdge a)) (edgesByOpenTo xs) = edgesByOpenTo (map (qualifyEdge a) xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases "edge_to x")
    case (GroundPort qp)
    then show ?thesis
      using Cons by simp
  next
    case (OpenPort p)
    moreover have "Mapping.keys (edgesByOpenTo (map (qualifyEdge a) xs)) = Mapping.keys (edgesByOpenTo xs)"
      using keys_map_values Cons by metis
    ultimately show ?thesis
      using Cons
      by (cases "p \<in> Mapping.keys (edgesByOpenTo xs)")
         (simp_all add: map_default_def default_def map_values_map_entry_Cons map_values_update)
  qed
qed

lemma edgesByOpenTo_simple_keys:
  assumes "length ps = length xs"
  shows "Mapping.keys (edgesByOpenTo (map2 Edge xs (map OpenPort ps))) = set ps"
  using assms
proof (induct xs arbitrary: ps)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (clarsimp simp add: length_Suc_conv)
qed

subsubsection\<open>Edges From Open Ports\<close>
(* Do the mirror for open inputs *)
primrec edgesByOpenFrom :: "('s, 'a, 'p) edge list \<Rightarrow> (('s, 'a) port, ('s, 'a, 'p) edge list) mapping"
  where
    "edgesByOpenFrom [] = Mapping.empty"
  | "edgesByOpenFrom (e#es) =
    ( if place_open (edge_from e)
        then Mapping.map_default (place_port (edge_from e)) Nil (Cons e) (edgesByOpenFrom es)
        else edgesByOpenFrom es
    )"

lemma edgesByOpenFrom_Some_preserve:
  assumes "\<exists>z. Mapping.lookup (edgesByOpenFrom es) p = Some z"
  shows "\<exists>z. Mapping.lookup (edgesByOpenFrom (e # es)) p = Some z"
  using assms by (metis edgesByOpenFrom.simps(2) lookup_map_default lookup_map_default_neq)

lemma edgesByOpenFrom_Some_ex:
  assumes "e \<in> set es"
      and "place_open (edge_from e)"
      and "place_port (edge_from e) = p"
    shows "\<exists>zs. Mapping.lookup (edgesByOpenFrom es) p = Some zs"
  using assms
proof (induct es)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    using Cons
    by (cases "e = x")
       (simp_all add: lookup_map_default lookup_map_default')
qed

lemma edgesByOpenFrom_in_result:
  assumes "e \<in> set es"
      and "Mapping.lookup (edgesByOpenFrom es) p = Some zs"
      and "place_open (edge_from e)"
      and "place_port (edge_from e) = p"
    shows "e \<in> set zs"
  using assms
proof (induct es arbitrary: zs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases "e = x")
    case True
    then show ?thesis
      using Cons by (fastforce simp add: lookup_map_default)
  next
    case e: False

    show ?thesis
    proof (cases "edge_from x")
      case (GroundPort qp)
      then show ?thesis
        using Cons e by simp
    next
      case (OpenPort p')
      then show ?thesis
      proof (cases "p' = p")
        case True
        then show ?thesis
          using Cons e OpenPort
          by (simp add: lookup_map_default lookup_default_def)
             (metis edgesByOpenFrom_Some_ex list.set_intros(2) option.simps(5))
      next
        case False
        then show ?thesis
          using Cons e OpenPort by (simp add: lookup_map_default_neq)
      qed
    qed
  qed
qed

lemma edgesByOpenFrom_Some:
  assumes "Mapping.lookup (edgesByOpenFrom es) p = Some xs"
  shows "xs = filter (\<lambda>x. edge_from x = OpenPort p) es"
  using assms
proof (induct es arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case
  proof (cases "edge_from a = OpenPort p")
    case True
    then show ?thesis
    proof (cases "Mapping.lookup (edgesByOpenFrom as) p")
      case None
      then show ?thesis
        using Cons True edgesByOpenFrom_Some_ex empty_filter_conv
        by (fastforce simp add: lookup_map_default lookup_default_def)
    next
      case (Some zs)
      then show ?thesis
        using Cons True by (simp add: lookup_map_default lookup_default_def)
    qed
  next
    case False
    then show ?thesis
      using Cons by (cases "edge_from a") (simp_all add: lookup_map_default_neq)
  qed
qed

text\<open>Edge from one of the collected edge lists must come from the input\<close>
lemma edgesByOpenFrom_in_values: (* TODO unused *)
  assumes "e \<in> set es"
      and "es \<in> snd ` Mapping.entries (edgesByOpenFrom xs)"
    shows "e \<in> set xs"
  using assms
  apply -
  apply (induct xs arbitrary: e es)
  apply simp
  apply (case_tac "place_open (edge_from a)" ; simp add: )
  apply clarsimp
  apply (subst (asm) entries_map_default)
  apply (case_tac "Mapping.lookup (edgesByOpenFrom xs) (place_port (edge_from a)) = None")
  using image_iff apply fastforce
  apply clarsimp
  by (metis image_eqI in_entriesI set_ConsD snd_conv)

lemma edgesByOpenFrom_qualify:
  "Mapping.map_values (\<lambda>k. map (qualifyEdge a)) (edgesByOpenFrom xs) = edgesByOpenFrom (map (qualifyEdge a) xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases "edge_from x")
    case (GroundPort qp)
    then show ?thesis
      using Cons by simp
  next
    case (OpenPort p)
    moreover have "Mapping.keys (edgesByOpenFrom (map (qualifyEdge a) xs)) = Mapping.keys (edgesByOpenFrom xs)"
      using keys_map_values Cons by metis
    ultimately show ?thesis
      using Cons
      by (cases "p \<in> Mapping.keys (edgesByOpenFrom xs)")
         (simp_all add: map_default_def default_def map_values_map_entry_Cons map_values_update)
  qed
qed

lemma edgesByOpenFrom_simple_keys:
  assumes "length ps = length xs"
  shows "Mapping.keys (edgesByOpenFrom (map2 Edge (map OpenPort ps) xs)) = set ps"
  using assms
proof (induct xs arbitrary: ps)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (clarsimp simp add: length_Suc_conv)
qed

(* We know one side of the edge for both generated lists, so we can just keep the other places *)
lemma edgesByOpenTo_edge_to:
  assumes "Mapping.lookup (edgesByOpenTo xs) p = Some es"
      and "e \<in> set es"
    shows "edge_to e = OpenPort p"
  using assms
proof (induct xs arbitrary: p es e)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    using edgesByOpenTo_Some
    by (metis (mono_tags, lifting) mem_Collect_eq set_filter)
qed

lemma edgesByOpenTo_forget_inv:
  defines "forget \<equiv> \<lambda>xs. Mapping.map_values (\<lambda>k. map edge_from) xs"
      and "free \<equiv> \<lambda>xs. Mapping.map_values (\<lambda>k. map (\<lambda>f. Edge f (OpenPort k))) xs"
    shows "free (forget (edgesByOpenTo xs)) = edgesByOpenTo xs"
  unfolding forget_def free_def
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (simp add: map_values_comp comp_def)
       (metis (no_types, lifting) map_values_is_idI edge.exhaust edge.sel(1,2)
         edgesByOpenTo.simps(2) edgesByOpenTo_edge_to list.map_ident_strong)
qed

lemma edgesByOpenFrom_edge_from:
  assumes "Mapping.lookup (edgesByOpenFrom xs) p = Some es"
      and "e \<in> set es"
    shows "edge_from e = OpenPort p"
  using assms
proof (induct xs arbitrary: p es e)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    using edgesByOpenFrom_Some
    by (metis (mono_tags, lifting) mem_Collect_eq set_filter)
qed

lemma edgesByOpenFrom_forget_inv:
  defines "forget \<equiv> \<lambda>xs. Mapping.map_values (\<lambda>k. map edge_to) xs"
      and "free \<equiv> \<lambda>xs. Mapping.map_values (\<lambda>k. map (\<lambda>f. Edge (OpenPort k) f)) xs"
    shows "free (forget (edgesByOpenFrom xs)) = edgesByOpenFrom xs"
  unfolding forget_def free_def
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (simp add: map_values_comp comp_def)
       (metis (no_types, lifting) map_values_is_idI edge.exhaust edge.sel(1,2)
         edgesByOpenFrom.simps(2) edgesByOpenFrom_edge_from list.map_ident_strong)
qed

subsubsection\<open>All Combinations of Edges from Place Lists\<close>

(* Build all edges possible from two lists of places in given order *)
primrec allEdges :: "('s, 'a, 'p) place list \<Rightarrow> ('s, 'a, 'p) place list \<Rightarrow> ('s, 'a, 'p) edge list"
  where
    "allEdges [] ts = []"
  | "allEdges (f#fs) ts = map (\<lambda>t. Edge f t) ts @ allEdges fs ts"

lemma allEdges_alt:
  "allEdges xs ys = concat (map (\<lambda>f. map (\<lambda>t. Edge f t) ys) xs)"
  by (induct xs ; simp)

lemma set_allEdges_remdups:
  "set (allEdges (remdups xs) (remdups ys)) = set (allEdges xs ys)"
  by (simp add: allEdges_alt)

(* Edges start and end in places from the respective inputs *)
lemma
  assumes "e \<in> set (allEdges xs ys)"
    shows allEdges_edge_from: "edge_from e \<in> set xs"
      and allEdges_edge_to: "edge_to e \<in> set ys"
  using assms by (induct xs arbitrary: e ; fastforce)+

lemma allEdges_Nil2 [simp]:
  "allEdges xs [] = []"
  by (induct xs ; simp)

(* This produces distinct outputs if both input list are distinct *)
lemma distinct_allEdges:
  assumes "distinct xs"
      and "distinct ys"
    shows "distinct (allEdges xs ys)"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    using allEdges_edge_from allEdges_edge_to
    by (fastforce simp add: distinct_map inj_on_def)
qed
(* Inverse is not as constrained, but that does not seem important *)

lemma renameEdge_allEdges [simp]:
  "map (renameEdge f) (allEdges xs ys) = allEdges (map (renamePlace f) xs) (map (renamePlace f) ys)"
  by (induct xs ; simp)

subsubsection\<open>Matching Edges from Two Port Mappings\<close>

(*
  Because the place lists will be very small it is reasonable to use remdups to make them distinct.
  It would be much more costly to do on the full list of edges produced once we're done.
  This also matches intuition well: we make an edge for any places indirectly connected through that
  shared open port, not really for every edge incident on it.

  But this is not enough, we will still need to remove duplicates after producing the edges.
  This is because in specific situations duplicates may be introduced by distinct ports.
  For instance, consider composing port graphs looking like < and >, which would yield duplicates =
  rather than the non-duplicated - but which cannot be detected when looking only at one port of the
  interface.
  (TODO: maybe we can detect those situations and prevent the need for this remdups?)
  (TODO: is it better for performance to do remdups before and after, or just after?)
  The possible issue is, as with sorting, in proving things through an application of remdups.
 *)

(* Querying a list of ports, build all edges for each from two port-place mappings *)
(* Note: each port needs to be output on one side and input on the other *)

(* TODO is there a way to generalise this to operate any sides?
  would need a notion of complementary sides to abstract the relationship between In and Out to arbitrary sides
 *)
primrec edgesFromPortMapping ::
  " ('s :: side_in_out, 'a) port list
  \<Rightarrow> (('s, 'a) port, ('s, 'a, 'p) place list) mapping
  \<Rightarrow> (('s, 'a) port, ('s, 'a, 'p) place list) mapping
  \<Rightarrow> ('s, 'a, 'p) edge list"
  where
    "edgesFromPortMapping [] x y = []"
  | "edgesFromPortMapping (p#ps) x y =
    ( case Mapping.lookup x (portSetSide Out p) of
        None \<Rightarrow> []
      | Some xs \<Rightarrow> (case Mapping.lookup y (portSetSide In p) of
          None \<Rightarrow> []
        | Some ys \<Rightarrow> allEdges xs ys))
    @ edgesFromPortMapping ps x y"

lemma edgesFromPortMapping_append:
  "edgesFromPortMapping (ps @ qs) x y = edgesFromPortMapping ps x y @ edgesFromPortMapping qs x y"
  by (induct ps ; simp)

text\<open>Every edge built from port mappings has origin in the flattened range of the first mapping\<close>
lemma edgesFromPortMapping_from_in:
  "e \<in> set (edgesFromPortMapping ps xs ys) \<Longrightarrow> edge_from e \<in> (\<Union>x \<in> snd ` Mapping.entries xs. set x)"
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case by simp (metis allEdges_edge_from in_entriesI snd_conv)
qed

text\<open>Every edge built from port mappings has target in the flattened range of the second mapping\<close>
lemma edgesFromPortMapping_to_in:
  "e \<in> set (edgesFromPortMapping ps xs ys) \<Longrightarrow> edge_to e \<in> (\<Union>x \<in> snd ` Mapping.entries ys. set x)"
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case by simp (metis allEdges_edge_to in_entriesI snd_conv)
qed

(* TODO doc *)
lemma edgesFromPortMapping_in_set_nthE:
  assumes "e \<in> set (edgesFromPortMapping ps m_xs m_ys)"
  obtains i j k xs ys
  where "Mapping.lookup m_xs (portSetSide Out (ps ! i)) = Some xs"
    and "Mapping.lookup m_ys (portSetSide In (ps ! i)) = Some ys"
    and "i < length ps"
    and "e = Edge (xs ! j) (ys ! k)"
    and "j < length xs"
    and "k < length ys"
  using assms
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case
  proof (cases "e \<in> set (edgesFromPortMapping ps m_xs m_ys)")
    case True
    then show ?thesis
      using Cons by simp (metis Suc_mono nth_Cons_Suc)
  next
    case False
    then show ?thesis
      using Cons
      by simp
         (metis allEdges_edge_from allEdges_edge_to edge.exhaust_sel in_set_conv_nth nth_Cons_0 zero_less_Suc)
  qed
qed

lemma edgesFromPortMapping_setI:
  assumes "p \<in> set ps"
      and "Mapping.lookup m_xs (portSetSide Out p) = Some xs"
      and "Mapping.lookup m_ys (portSetSide In p) = Some ys"
      and "x \<in> set xs"
      and "y \<in> set ys"
      and "e = Edge x y"
    shows "e \<in> set (edgesFromPortMapping ps m_xs m_ys)"
  using assms
proof (induct ps arbitrary: p x y xs ys)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case
    by (fastforce simp add: allEdges_alt)
qed

lemma renameEdge_edgesFromPortMapping:
  " map (renameEdge f) (edgesFromPortMapping ps m_xs m_ys) =
    edgesFromPortMapping ps (Mapping.map_values (\<lambda>_. map (renamePlace f)) m_xs) (Mapping.map_values (\<lambda>_. map (renamePlace f)) m_ys)"
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case
  proof (cases "Mapping.lookup m_xs (portSetSide Out a)")
    case None
    then show ?thesis using Cons by (simp add: lookup_map_values)
  next
    case x: (Some x)
    then show ?thesis
    proof (cases "Mapping.lookup m_ys (portSetSide In a)")
      case None
      then show ?thesis using Cons x by (simp add: lookup_map_values)
    next
      case (Some y)
      then show ?thesis using Cons x by (simp add: lookup_map_values)
    qed
  qed
qed

lemma qualifyEdge_edgesFromPortMapping:
  " map (qualifyEdge a) (edgesFromPortMapping ps m_xs m_ys) =
    edgesFromPortMapping ps (Mapping.map_values (\<lambda>_. map (qualifyPlace a)) m_xs) (Mapping.map_values (\<lambda>_. map (qualifyPlace a)) m_ys)"
  unfolding qualifyPlace_rename qualifyEdge_rename
  by (rule renameEdge_edgesFromPortMapping)

lemma edgesFromPortMapping_deleteL:
  assumes "a \<notin> portSetSide Out ` set ps"
    shows "edgesFromPortMapping ps xs ys = edgesFromPortMapping ps (Mapping.delete a xs) ys"
  using assms by (induct ps ; simp)

lemma edgesFromPortMapping_deleteR:
  assumes "a \<notin> portSetSide In ` set ps"
    shows "edgesFromPortMapping ps xs ys = edgesFromPortMapping ps xs (Mapping.delete a ys)"
  using assms
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case by (cases "Mapping.lookup xs (portSetSide Out a)") simp_all
qed

subsubsection\<open>Stitching the Edges\<close>

text\<open>
  Given two port graphs, we connect the outgoing edges of one with the incoming edges of the other
  by matching them on the open output ports of the first.
  (It should be equivalent matching them on the open input ports of the second, because in cases
  we expect those two collections mirror each other.)

  To do this on port graphs @{term x} and @{term y} we:
  \<^item> Pick out edges from @{term x} going to open ports, grouped by those ports
  \<^item> Pick out edges from @{term y} going from open ports, grouped by those ports
  \<^item> Knowing the open port means we know one side of each edge, so we only care about the other
    place. So we drop the part of each edge we know, arriving at places grouped by ports.
  \<^item> Drop any duplicate places for a given port, which is simple to perform because there will rarely
    be even two to compare.
  \<^item> Match the two bucketed collections of places on the open ports (i.e.\ the buckets), using the
    @{const Out} variant for the first and @{const In} variant for the second (aimed at sequential
    composition, so other sides are unused).
  \<^item> Construct edges from all possible combinations of edges meeting at one open port.
  \<^item> Drop any duplicate edges resulting from the process.
\<close>
fun seqInterfaceEdges :: "('s :: side_in_out, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p) edge list"
  where "seqInterfaceEdges x y =
  remdups
    ( edgesFromPortMapping (filter (\<lambda>x. port.side x = Out) (pg_ports x))
      ( Mapping.map_values (\<lambda>k. map edge_from) (edgesByOpenTo (pg_edges x)))
      ( Mapping.map_values (\<lambda>k. map edge_to) (edgesByOpenFrom (pg_edges y))))"

text\<open>This process produces no duplicates, trivially by its last step\<close>
lemma distinct_seqInterfaceEdges:
  "distinct (seqInterfaceEdges x y)"
  by simp

text\<open>Every connected edge comes from edges in the inputs which share a place\<close>
lemma seqInterfaceEdges_setD:
  fixes x y :: "('s :: side_in_out, 'a, 'p, 'l) port_graph"
  assumes "e \<in> set (seqInterfaceEdges x y)"
  obtains a b and p :: "('s, 'a) port"
    where "edge_from e = edge_from a" and "a \<in> set (pg_edges x)"
      and "edge_to e = edge_to b" and "b \<in> set (pg_edges y)"
      and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
      and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
      and "port.side p = Out"
proof -
  let ?ps = "filter (\<lambda>x. port.side x = Out) (pg_ports x)"
  let ?m_xs = "Mapping.map_values (\<lambda>k. map edge_from) (edgesByOpenTo (pg_edges x))"
  let ?m_ys = "Mapping.map_values (\<lambda>k. map edge_to) (edgesByOpenFrom (pg_edges y))"

  obtain i j k xs ys
  where xs: "Mapping.lookup ?m_xs (portSetSide Out (?ps ! i)) = Some xs"
    and ys: "Mapping.lookup ?m_ys (portSetSide In (?ps ! i)) = Some ys"
    and i: "i < length ?ps"
    and e: "e = Edge (xs ! j) (ys ! k)"
    and j: "j < length xs"
    and k: "k < length ys"
    using assms by simp (elim edgesFromPortMapping_in_set_nthE)

  show ?thesis
  proof
    let ?a = "Edge (xs ! j) (OpenPort (portSetSide Out (?ps ! i)))"
    let ?b = "Edge (OpenPort (portSetSide In (?ps ! i))) (ys ! k)"
    let ?p = "?ps ! i"

    show "edge_from e = edge_from ?a"
      using e by simp
    show "?a \<in> set (pg_edges x)"
      using xs j
      by (clarsimp simp add: lookup_map_values elim!: edgesByOpenTo_Some[elim_format])
         (metis (mono_tags, lifting) edge.collapse mem_Collect_eq nth_mem set_filter)
    show "edge_to e = edge_to ?b"
      using e by simp
    show "?b \<in> set (pg_edges y)"
      using ys k
      by (clarsimp simp add: lookup_map_values elim!: edgesByOpenFrom_Some[elim_format])
         (metis (mono_tags, lifting) edge.collapse mem_Collect_eq nth_mem set_filter)
    show "edge_to ?a = OpenPort (portSetSide Out ?p)"
      by simp
    show "edge_in_flow ?a"
      by (simp add: edge_in_flow_def)
    show "edge_from ?b = OpenPort (portSetSide In ?p)"
      by simp
      show "edge_in_flow ?b"
      by (simp add: edge_in_flow_def)
    show "port.side ?p = Out"
      using i nth_mem by fastforce
  qed
qed

text\<open>
  In well-formed port graphs with flow, any edges from the two inputs that meet at corresponding
  interface ports yield a connected edge.
\<close>
(* Note: in the following p has to be output of x, because of a choice we made in seqInterfaceEdges definition *)
lemma seqInterfaceEdges_setI:
  assumes "port_graph_flow x"
      and "port_graph_flow y"
      and "edge_from e = edge_from a" and "a \<in> set (pg_edges x)"
      and "edge_to e = edge_to b" and "b \<in> set (pg_edges y)"
      and "edge_to a = OpenPort (portSetSide Out p)"
      and "edge_from b = OpenPort (portSetSide In p)"
    shows "e \<in> set (seqInterfaceEdges x y)"
proof -
  obtain xs where xs: "Mapping.lookup (edgesByOpenTo (pg_edges x)) (portSetSide Out p) = Some xs"
    using assms(4,7) edgesByOpenTo_Some_ex by fastforce
  obtain ys where ys: "Mapping.lookup (edgesByOpenFrom (pg_edges y)) (portSetSide In p) = Some ys"
    using assms(6,8) edgesByOpenFrom_Some_ex by fastforce

  have "portSetSide Out p \<in> set (filter (\<lambda>x. port.side x = Out) (pg_ports x))"
    using assms(1,4,7) port_graph.edge_to_pg port_graph_flow_def by fastforce
  moreover have "edge_from a \<in> set (map edge_from xs)"
    using assms(4,7) edgesByOpenTo_in_result xs by fastforce
  moreover have "edge_to b \<in> set (map edge_to ys)"
    using assms(6,8) edgesByOpenFrom_in_result ys by fastforce
  moreover have "e = Edge (edge_from a) (edge_to b)"
    using assms(3,5) by (metis edge.collapse)
  ultimately show ?thesis
    using xs ys by (fastforce intro: edgesFromPortMapping_setI simp add: lookup_map_values)
qed

text\<open>
  If we can rename edges of two port graphs into edges of two other port graphs, then any edge from
  the former pair's interface can be renamed to an edge of the latter pair's interface.
\<close>
(* TODO this is probably underused in proofs, being a later addition *)
lemma seqInterfaceEdges_set_rename:
  fixes f e and x y x' y' :: "('s :: side_in_out, 'a, 'p, 'l) port_graph"
  assumes "port_graph_flow x'"
      and "port_graph_flow y'" 
      and "e \<in> set (seqInterfaceEdges x y)" 
      and "\<And>e. e \<in> set (pg_edges x) \<Longrightarrow> renameEdge f e \<in> set (pg_edges x')" 
      and "\<And>e. e \<in> set (pg_edges y) \<Longrightarrow> renameEdge f e \<in> set (pg_edges y')"
    shows "renameEdge f e \<in> set (seqInterfaceEdges x' y')"
proof -
  obtain a b and p :: "('s, 'a) port"
    where "edge_from e = edge_from a" and "a \<in> set (pg_edges x)"
      and "edge_to e = edge_to b" and "b \<in> set (pg_edges y)"
      and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
      and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
      and "port.side p = Out"
    using assms(3) seqInterfaceEdges_setD by blast
  note abp = this

  show ?thesis
    using assms(1,2)
  proof (rule seqInterfaceEdges_setI)
    show "edge_from (renameEdge f e) = edge_from (renameEdge f a)"
      using abp(1) by simp
    show "renameEdge f a \<in> set (pg_edges x')"
      using abp(2) assms(4) by blast
    show "edge_to (renameEdge f e) = edge_to (renameEdge f b)"
      using abp(3) by simp
    show "renameEdge f b \<in> set (pg_edges y')"
      using abp(4) assms(5) by blast
    show "edge_to (renameEdge f a) = OpenPort (portSetSide Out p)"
      using abp(5) by simp
    show "edge_from (renameEdge f b) = OpenPort (portSetSide In p)"
      using abp(7) by simp
  qed
qed

text\<open>Every connected edge has a corresponding edge in first input which shares its origin\<close>
lemma seqInterfaceEdges_from_ex_edge:
  assumes "e \<in> set (seqInterfaceEdges x y)"
  obtains e' where "edge_from e = edge_from e'" and "e' \<in> set (pg_edges x)" and "edge_in_flow e'"
  using seqInterfaceEdges_setD assms by blast

text\<open>Every connected edge has a corresponding edge in second input which shares its target\<close>
lemma seqInterfaceEdges_to_ex_edge:
  assumes "e \<in> set (seqInterfaceEdges x y)"
  obtains e' where "edge_to e = edge_to e'" and "e' \<in> set (pg_edges y)" and "edge_in_flow e'"
  using seqInterfaceEdges_setD assms by blast

lemma map_remdups: (* TODO general theorem *)
  "inj_on f (set xs) \<Longrightarrow> map f (remdups xs) = remdups (map f xs)"
  by (induct xs ; clarsimp)

lemma seqInterfaceEdges_qualify:
  "map (qualifyEdge a) (seqInterfaceEdges x y) = seqInterfaceEdges (qualifyPortGraph a x) (qualifyPortGraph a y)"
proof -
  have fr:
    " Mapping.map_values (\<lambda>k. map (qualifyPlace a \<circ> edge_from)) m
    = Mapping.map_values (\<lambda>k. map edge_from) (Mapping.map_values (\<lambda>k. map (qualifyEdge a)) m)"
    for m :: "(('a, 'b) port, ('a, 'b, 'c) edge list) mapping"
    by (simp add: comp_def map_values_comp)
  have to:
    " Mapping.map_values (\<lambda>k. map (qualifyPlace a \<circ> edge_to)) m
    = Mapping.map_values (\<lambda>k. map edge_to) (Mapping.map_values (\<lambda>k. map (qualifyEdge a)) m)"
    for m :: "(('a, 'b) port, ('a, 'b, 'c) edge list) mapping"
    by (simp add: comp_def map_values_comp)

  have "inj_on (qualifyEdge a) A" for A :: "('a, 'b, 'c) edge set"
    by (metis (lifting) inj_qualifyEdge inj_on_subset subset_UNIV)
  then show ?thesis
    by (simp add: map_remdups qualifyEdge_edgesFromPortMapping map_values_comp fr to
        edgesByOpenTo_qualify edgesByOpenFrom_qualify)
qed

text\<open>
  There exist well-formed port graphs such that the above process without its last step would yield
  duplicate edges, which is why the last step is necessary.
  This is because they may come from multiple open ports and thus cannot be detected (at least, I
  do not know how) before connection is done.
\<close>
lemma
  assumes "Edge p_x (OpenPort (portSetSide Out portA)) \<in> set (pg_edges x)"
      and "Edge p_x (OpenPort (portSetSide Out portB)) \<in> set (pg_edges x)"
      and "Edge (OpenPort (portSetSide In portA)) p_y \<in> set (pg_edges y)"
      and "Edge (OpenPort (portSetSide In portB)) p_y \<in> set (pg_edges y)"
      and "port.index portA \<noteq> port.index portB"
      and "port_graph_flow x"
      and "port_graph_flow y"
    shows "\<not> distinct
    ( edgesFromPortMapping (filter (\<lambda>x. port.side x = Out) (pg_ports x))
      ( Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
      ( Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))))"
proof -
  interpret x: port_graph_flow x using assms(6) .
  interpret y: port_graph_flow y using assms(7) .

  let ?f =
    " edgesFromPortMapping (filter (\<lambda>x. port.side x = Out) (pg_ports x))
      ( Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
      ( Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y)))"

    (* Places being of the port graphs is subsumed by them forming edges of well-formed graphs *)
    have portA_x: "portSetSide Out portA \<in> set (pg_ports x)"
      by (metis edge.sel(2) place.disc(4) place_port.simps(2) assms(1) x.edge_to_pg x.open_port_pg)
    have portB_x: "portSetSide Out portB \<in> set (pg_ports x)"
      by (metis edge.sel(2) place.disc(4) place_port.simps(2) assms(2) x.edge_to_pg x.open_port_pg)
    have portA_y: "portSetSide In portA \<in> set (pg_ports y)"
      by (metis edge.sel(1) place.disc(4) place_port.simps(2) assms(3) y.edge_from_pg y.open_port_pg)
    have portB_y: "portSetSide In portB \<in> set (pg_ports y)"
      by (metis edge.sel(1) place.disc(4) place_port.simps(2) assms(4) y.edge_from_pg y.open_port_pg)

    obtain iA iB
      where "filter (\<lambda>x. port.side x = Out) (pg_ports x) ! iA = portSetSide Out portA"
        and "iA < length (filter (\<lambda>x. port.side x = Out) (pg_ports x))"
        and "filter (\<lambda>x. port.side x = Out) (pg_ports x) ! iB = portSetSide Out portB"
        and "iB < length (filter (\<lambda>x. port.side x = Out) (pg_ports x))"
      using portA_x portB_x set_filter in_set_conv_nth portSetSide_side
      by (smt (verit) mem_Collect_eq)
    note port_indices = this

    have iA_neq_iB: "iA \<noteq> iB"

      using assms(5) port_indices
      by (metis port.collapse port.sel(2) portSetSide.simps)

    let ?m = "min iA iB"
    let ?n = "max iA iB"

    have "filter (\<lambda>x. port.side x = Out) (pg_ports x) =
      take ?m (filter (\<lambda>x. port.side x = Out) (pg_ports x)) @
      [filter (\<lambda>x. port.side x = Out) (pg_ports x) ! ?m] @
      drop (Suc ?m) (filter (\<lambda>x. port.side x = Out) (pg_ports x))"
      using port_indices iA_neq_iB by (simp add: Cons_nth_drop_Suc)
    then have "filter (\<lambda>x. port.side x = Out) (pg_ports x) =
      take ?m (filter (\<lambda>x. port.side x = Out) (pg_ports x)) @
      [filter (\<lambda>x. port.side x = Out) (pg_ports x) ! ?m] @
      take (?n - Suc ?m) (drop (Suc ?m) (filter (\<lambda>x. port.side x = Out) (pg_ports x))) @
      [filter (\<lambda>x. port.side x = Out) (pg_ports x) ! ?n] @
      drop (Suc ?n) (filter (\<lambda>x. port.side x = Out) (pg_ports x))"
      using port_indices iA_neq_iB
      by (smt (verit, del_insts) add_diff_inverse_nat append.assoc append_Cons append_Nil
          hd_drop_conv_nth id_take_nth_drop max.commute max_min_same(1) min.absorb3 min.absorb4
          nat_neq_iff not_less_eq take_add take_hd_drop)
    then have f_decomp: "?f =
      edgesFromPortMapping (take ?m (filter (\<lambda>x. port.side x = Out) (pg_ports x)))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))) @
      edgesFromPortMapping [filter (\<lambda>x. port.side x = Out) (pg_ports x) ! ?m]
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))) @
      edgesFromPortMapping (take (?n - Suc ?m) (drop (Suc ?m) (filter (\<lambda>x. port.side x = Out) (pg_ports x))))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))) @
      edgesFromPortMapping [filter (\<lambda>x. port.side x = Out) (pg_ports x) ! ?n]
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))) @
      edgesFromPortMapping (drop (Suc ?n) (filter (\<lambda>x. port.side x = Out) (pg_ports x)))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y)))"
      using edgesFromPortMapping_append by metis

    have "\<exists>xs. map_option (map edge_from) (Mapping.lookup (edgesByOpenTo (pg_edges x)) (portSetSide Out portA)) = Some xs"
      using assms(1) by (simp add: edgesByOpenTo_Some_ex)
    then obtain places_x_A
      where places_x_A: "map_option (map edge_from) (Mapping.lookup (edgesByOpenTo (pg_edges x)) (portSetSide Out portA)) = Some places_x_A"
      by blast

    have "\<exists>xs. map_option (map edge_from) (Mapping.lookup (edgesByOpenTo (pg_edges x)) (portSetSide Out portB)) = Some xs"
      using assms(2) by (simp add: edgesByOpenTo_Some_ex)
    then obtain places_x_B
      where places_x_B: "map_option (map edge_from) (Mapping.lookup (edgesByOpenTo (pg_edges x)) (portSetSide Out portB)) = Some places_x_B"
      by blast

    have "\<exists>xs. map_option (map edge_to) (Mapping.lookup (edgesByOpenFrom (pg_edges y)) (portSetSide In portA)) = Some xs"
      using assms(3) by (simp add: edgesByOpenFrom_Some_ex)
    then obtain places_y_A
      where places_y_A: "map_option (map edge_to) (Mapping.lookup (edgesByOpenFrom (pg_edges y)) (portSetSide In portA)) = Some places_y_A"
      by blast

    have "\<exists>xs. map_option (map edge_to) (Mapping.lookup (edgesByOpenFrom (pg_edges y)) (portSetSide In portB)) = Some xs"
      using assms(4) by (simp add: edgesByOpenFrom_Some_ex)
    then obtain places_y_B
      where places_y_B: "map_option (map edge_to) (Mapping.lookup (edgesByOpenFrom (pg_edges y)) (portSetSide In portB)) = Some places_y_B"
      by blast

    have "p_x \<in> set places_x_A"
      using places_x_A assms(1) edgesByOpenTo_in_result edgesByOpenTo_Some_ex
      by (metis (no_types, opaque_lifting) edge.sel(1,2) image_eqI list.set_map option.inject
          option.simps(9) place.disc(4) place_port.simps(2))
    moreover have "p_y \<in> set places_y_A"
      using places_y_A assms(3) edgesByOpenFrom_in_result edgesByOpenFrom_Some_ex
      by (metis (no_types, opaque_lifting) edge.sel(1,2) image_eqI list.set_map option.inject
          option.simps(9) place.disc(4) place_port.simps(2))
    ultimately have "Edge p_x p_y \<in> set (allEdges places_x_A places_y_A)"
      by (fastforce simp add: allEdges_alt)
    then have edge_in_sublist_iA:
      "Edge p_x p_y \<in> set (edgesFromPortMapping [filter (\<lambda>x. port.side x = Out) (pg_ports x) ! iA]
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))))"
      using places_x_A places_y_A port_indices(1)
      by (clarsimp simp add: comp_def lookup_map_values set_allEdges_remdups)
    then obtain jA
      where "edgesFromPortMapping [filter (\<lambda>x. port.side x = Out) (pg_ports x) ! iA]
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))) ! jA = Edge p_x p_y"
        and "jA < length (edgesFromPortMapping [filter (\<lambda>x. port.side x = Out) (pg_ports x) ! iA]
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))))"
      using in_set_conv_nth by metis
    note jA = this

    have "p_x \<in> set places_x_B"
      using places_x_B assms(2) edgesByOpenTo_in_result edgesByOpenTo_Some_ex
      by (metis (no_types, opaque_lifting) edge.sel(1,2) image_eqI list.set_map option.inject
          option.simps(9) place.disc(4) place_port.simps(2))
    moreover have "p_y \<in> set places_y_B"
      using places_y_B assms(4) edgesByOpenFrom_in_result edgesByOpenFrom_Some_ex
      by (metis (no_types, opaque_lifting) edge.sel(1,2) image_eqI list.set_map option.inject
          option.simps(9) place.disc(4) place_port.simps(2))
    ultimately have "Edge p_x p_y \<in> set (allEdges places_x_B places_y_B)"
      by (fastforce simp add: allEdges_alt)
    then have edge_in_sublist_iB:
      "Edge p_x p_y \<in> set (edgesFromPortMapping [filter (\<lambda>x. port.side x = Out) (pg_ports x) ! iB]
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))))"
      using places_x_B places_y_B port_indices(3)
      by (clarsimp simp add: comp_def lookup_map_values set_allEdges_remdups)
    then obtain jB
      where "edgesFromPortMapping [filter (\<lambda>x. port.side x = Out) (pg_ports x) ! iB]
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))) ! jB = Edge p_x p_y"
        and "jB < length (edgesFromPortMapping [filter (\<lambda>x. port.side x = Out) (pg_ports x) ! iB]
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
          (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))))"
      using in_set_conv_nth by metis
    note jB = this

    (*
      First duplicate index is length of prefix plus jA or jB, depending on if ?m is iA or iB.
      Second duplicate index is length of prefix, first sublist and infix plus jA or jB, depending on if ?n is iA or iB.
     *)
    obtain dup1 dup2
      where "?f ! dup1 = Edge p_x p_y" and "dup1 < length ?f"
        and "?f ! dup2 = Edge p_x p_y" and "dup2 < length ?f"
        and "dup1 \<noteq> dup2"
    proof (cases "iA < iB")
      case True
      then have mn: "?m = iA" "?n = iB"
        by simp_all

      let ?dup1 =
        " length (edgesFromPortMapping
           (take (min iA iB) (filter (\<lambda>x. port.side x = Out) (pg_ports x)))
           (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
           (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))))
          + jA"
      let ?dup2 =
        " length (
            edgesFromPortMapping
             (take (min iA iB) (filter (\<lambda>x. port.side x = Out) (pg_ports x)))
             (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
             (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))) @
            edgesFromPortMapping [filter (\<lambda>x. port.side x = Out) (pg_ports x) ! min iA iB]
             (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
             (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))) @
            edgesFromPortMapping
             (take (max iA iB - Suc (min iA iB))
               (drop (Suc (min iA iB)) (filter (\<lambda>x. port.side x = Out) (pg_ports x))))
             (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
             (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))))
          + jB"

      have "?f ! ?dup1 = Edge p_x p_y"
        using jA(1,2) f_decomp mn(1) by (simp add: nth_append)
      moreover have "?dup1 < length ?f"
        using f_decomp jA(2) mn(1) by fastforce
      moreover have "?f ! ?dup2 = Edge p_x p_y"
        using jB(1,2) f_decomp mn(1) by (simp add: nth_append)
      moreover have "?dup2 < length ?f"
        using f_decomp jB(2) mn(1) by fastforce
      moreover have "?dup1 \<noteq> ?dup2"
        using jA(2) mn(1) by simp
      ultimately show ?thesis
        by (rule that)
  next
    case False
    then have mn: "?m = iB" "?n = iA"
      by simp_all

    let ?dup1 =
      " length (edgesFromPortMapping
         (take (min iA iB) (filter (\<lambda>x. port.side x = Out) (pg_ports x)))
         (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
         (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))))
        + jB"
    let ?dup2 =
      " length (
          edgesFromPortMapping
           (take (min iA iB) (filter (\<lambda>x. port.side x = Out) (pg_ports x)))
           (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
           (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))) @
          edgesFromPortMapping [filter (\<lambda>x. port.side x = Out) (pg_ports x) ! min iA iB]
           (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
           (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))) @
          edgesFromPortMapping
           (take (max iA iB - Suc (min iA iB))
             (drop (Suc (min iA iB)) (filter (\<lambda>x. port.side x = Out) (pg_ports x))))
           (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_from) (edgesByOpenTo (pg_edges x)))
           (Mapping.map_values (\<lambda>k. remdups \<circ> map edge_to) (edgesByOpenFrom (pg_edges y))))
        + jA"

      have "?f ! ?dup1 = Edge p_x p_y"
        using jB(1,2) f_decomp mn(1) by (simp add: nth_append)
      moreover have "?dup1 < length ?f"
        using f_decomp jB(2) mn(1) by fastforce
      moreover have "?f ! ?dup2 = Edge p_x p_y"
        using jA(1,2) f_decomp mn(1) by (simp add: nth_append)
      moreover have "?dup2 < length ?f"
        using f_decomp jA(2) mn(1) by fastforce
      moreover have "?dup1 \<noteq> ?dup2"
        using jB(2) mn(1) by simp
      ultimately show ?thesis
        by (rule that)
  qed
  then show ?thesis
    by (metis distinct_conv_nth)
qed

text\<open>
  Such a pair of port graphs exists, essentially the shapes < and > with one node each.
  That node was needed to satisfy an assumption of port graphs that was since removed.
\<close>
lemma
  obtains x y :: "('s :: side_in_out, nat, nat, nat) port_graph"
      and p_x p_y
      and portA portB :: "('s, nat) port"
    where "Edge p_x (OpenPort (portSetSide Out portA)) \<in> set (pg_edges x)"
      and "Edge p_x (OpenPort (portSetSide Out portB)) \<in> set (pg_edges x)"
      and "Edge (OpenPort (portSetSide In portA)) p_y \<in> set (pg_edges y)"
      and "Edge (OpenPort (portSetSide In portB)) p_y \<in> set (pg_edges y)"
      and "port.index portA \<noteq> port.index portB"
      and "port_graph_flow x"
      and "port_graph_flow y"
proof -
  define In :: 's where [simp]: "In \<equiv> side_in_out_class.In"
  define Out :: 's where [simp]: "Out \<equiv> side_in_out_class.Out"

  let ?nX = "Node [] 0 [Port Out 0 0]"
  let ?p_x = "GroundPort (QPort (Port Out 0 0) [])"
  let ?nY = "Node [] 0 [Port In 0 0]"
  let ?p_y = "GroundPort (QPort (Port In 0 0) [])"
  let ?portA = "Port Out 0 0"
  let ?portB = "Port Out 1 1"
  let ?x = "PGraph
    [?nX]
    [ Edge ?p_x (OpenPort ?portA)
    , Edge ?p_x (OpenPort ?portB)
    ]
    [?portA, ?portB]"
  let ?y = "PGraph
    [?nY]
    [ Edge (OpenPort (portSetSide In ?portA)) ?p_y
    , Edge (OpenPort (portSetSide In ?portB)) ?p_y
    ]
    [portSetSide In ?portA, portSetSide In ?portB]"

  show ?thesis
    apply (rule that[of ?p_x ?portA ?x ?portB ?p_y ?y])
    by unfold_locales fastforce+
qed

subsection\<open>Sequencing Port Graphs\<close>

text\<open>
  Sequential composition of port graphs assumed to be qualified apart:
  \<^item> Nodes are those of LHS and RHS.
  \<^item> Edges are:
    \<^item> Edges resulting from connecting the interface,
    \<^item> Edges of LHS that were not connected to its outputs,
    \<^item> Edges of RHS that were not connected to its input with non-flow open ports shifted up to match the new open ports (see below).
  \<^item> Open ports are:
    \<^item> Non-output ports of LHS,
    \<^item> Output ports of RHS,
    \<^item> Non-input and non-output ports of RHS shifted up within each side to avoid overlap with ports
      of that side coming from LHS.
\<close>
fun seqPortGraphs :: "('s :: side_in_out, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) port_graph"
  where "seqPortGraphs x y = PGraph
    (pg_nodes x @ pg_nodes y)
    ( seqInterfaceEdges x y @
      disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = Out) (pg_ports x))) (pg_edges x) @
      map (shiftOpenInEdge
            (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
            (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))))
        (disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = In) (pg_ports y))) (pg_edges y)))
    ( filter (\<lambda>x. port.side x \<noteq> Out) (pg_ports x)
    @ filter (\<lambda>x. port.side x = Out) (pg_ports y)
    @ map (shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x))))
        (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out) (pg_ports y)))"

text\<open>The disconnecting can be simplified when relevant side is a well-behaved port graph with flow\<close>
lemma seqPortGraphs_flow_edges:
  assumes "port_graph_flow x"
      and "port_graph_flow y"
    shows "pg_edges (seqPortGraphs x y) =
      seqInterfaceEdges x y @
      filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x) @
      map (shiftOpenInEdge
            (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
            (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))))
        (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y))"
  using assms
  by (clarsimp simp add: port_graph_flow.disconnect_out port_graph_flow.disconnect_in)

lemma seqPortGraphs_filter_ports [simp]:
  "filter (\<lambda>x. port.side x = In) (pg_ports (seqPortGraphs x y)) = filter (\<lambda>x. port.side x = In) (pg_ports x)"
  "filter (\<lambda>x. port.side x = Out) (pg_ports (seqPortGraphs x y)) = filter (\<lambda>x. port.side x = Out) (pg_ports y)"
  "filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out) (pg_ports (seqPortGraphs x y))
  = filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out) (pg_ports x)
    @ map (\<lambda>q. shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x))) q)
        (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out) (pg_ports y))"
  by (simp_all add: conj_comms) (metis in_out_distinct)+

text\<open>
  An edge of sequential composition of port graphs is either:
  \<^item> Result of connecting interface edges, or
  \<^item> Edge of the left-hand side that does not go to an open output, or
  \<^item> Edge of the right-hand side that does not come from an open input.
\<close>
lemma seqPortGraphs_edge_cases [consumes 3, case_names Stitch L R]:
  assumes "port_graph_flow x"
      and "port_graph_flow y"
      and "e \<in> set (pg_edges (seqPortGraphs x y))"
  obtains
    (Stitch) "e \<in> set (seqInterfaceEdges x y)"
  | (L) "e \<in> set (pg_edges x)" and "\<not> toOpenOut e"
  | (R) e' where "e' \<in> set (pg_edges y)" and "\<not> fromOpenIn e'"
      and "e = shiftOpenInEdge
            (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
            (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
            e'"
  using assms
  by (fastforce simp add: port_graph_flow.disconnect_out port_graph_flow.disconnect_in)

text\<open>Nodes of sequential composition are nodes of either component\<close>
lemma in_nodes_seqPortGraphsE:
  assumes "n \<in> set (pg_nodes (seqPortGraphs x y))"
  obtains "n \<in> set (pg_nodes x)" | "n \<in> set (pg_nodes y)"
  using assms by fastforce

text\<open>Port graph is disjoint from sequential composition if it is disjoint from each component\<close>
lemma pg_disjoint_seqPortGraphs [simp]:
  "pg_disjoint (seqPortGraphs x y) z = (pg_disjoint x z \<and> pg_disjoint y z)"
  "pg_disjoint z (seqPortGraphs x y) = (pg_disjoint z x \<and> pg_disjoint z y)"
  by (fastforce simp add: pg_disjoint_def)+

lemma pgraphPlaces_seqPortGraphs:
  " pgraphPlaces (seqPortGraphs x y) =
    filter (\<lambda>x. place_ground x) (pgraphPlaces x @ pgraphPlaces y) @
    filter (\<lambda>x. place_open x \<and> place_side x \<noteq> Out) (pgraphPlaces x) @
    filter (\<lambda>x. place_open x \<and> place_side x = Out) (pgraphPlaces y) @
    map (\<lambda>q. shiftOpenPlace (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x))) q)
      (filter (\<lambda>x. place_open x \<and> place_side x \<noteq> In \<and> place_side x \<noteq> Out) (pgraphPlaces y))"
  by (simp add: filter_map comp_def)

text\<open>
  Sequential composition of port graphs with flow that have distinct node paths produces again a
  port graph with flow.
\<close>
lemma port_graph_flow_seqPortGraphs:
  fixes x y :: "('s :: side_in_out, 'a, 'p, 'l) port_graph"
  assumes "port_graph_flow x"
      and "port_graph_flow y"
      and "pg_disjoint x y"
    shows "port_graph_flow (seqPortGraphs x y)"
proof -
  interpret x: port_graph_flow x using assms by simp
  interpret y: port_graph_flow y using assms by simp

  show ?thesis
  proof
    fix e
    assume e: "e \<in> set (pg_edges (seqPortGraphs x y))"

    from assms(1,2) e show "edge_from e \<in> set (pgraphPlaces (seqPortGraphs x y))"
    proof (cases rule: seqPortGraphs_edge_cases)
      case Stitch
      then show ?thesis
      proof (cases "edge_from e")
        case (GroundPort qp)
        then have "edge_from e \<in> set (filter (\<lambda>x. place_ground x) (pgraphPlaces x))"
          using Stitch x.edge_from_pg by (fastforce elim!: seqInterfaceEdges_setD)
        then show ?thesis
          by (fastforce simp add: pgraphPlaces_seqPortGraphs)
      next
        case (OpenPort p)
        then have "edge_from e \<in> set (filter (\<lambda>x. place_open x \<and> place_side x \<noteq> Out) (pgraphPlaces x))"
          using Stitch x.edge_from_pg x.edge_from_open seqInterfaceEdges_from_ex_edge
          by (metis (mono_tags, lifting) in_out_distinct mem_Collect_eq place.disc(4) set_filter)
        then show ?thesis
          by (fastforce simp add: pgraphPlaces_seqPortGraphs)
      qed
    next
      case L
      then show ?thesis
        using x.edge_from_pg pgraphPlaces_seqPortGraphs x.edge_from_open edge_in_flowI(2)
        by (metis (mono_tags, lifting) Un_iff in_out_distinct mem_Collect_eq place.exhaust_disc set_append set_filter)
    next
      case (R e')
      then show ?thesis
      proof (cases "edge_from e")
        case (GroundPort qp)
        moreover have "edge_from e = edge_from e'"
          using R(3) GroundPort
          by (metis (no_types, lifting) place.disc(1) shiftOpenInEdge_simps(1) shiftOpenPlace_ground)
        ultimately show ?thesis
          using R y.edge_from_pg pgraphPlaces_seqPortGraphs
          by (metis (no_types, lifting) Un_iff filter_set member_filter place.disc(1) set_append)
      next
        case (OpenPort p)

        have from_eq: "edge_from e = shiftOpenPlace (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (edge_from e')"
          using R(3) OpenPort shiftOpenInEdge_simps(1) by blast
        have side_eq: "place_side (edge_from e) = place_side (edge_from e')"
          using from_eq by (metis (no_types, lifting) shiftOpenPlace_side)

        have "edge_from e' \<in> set (pgraphPlaces y)"
          using R(1) y.edge_from_pg by metis
        moreover have op: "place_open (edge_from e')"
          using from_eq OpenPort shiftOpenPlace_open(1) by (metis (no_types, lifting) place_open_def)
        moreover have "place_side (edge_from e) \<noteq> In"
          using R OpenPort fromOpenInI shiftOpenInEdge_fromOpenIn
          by (metis (no_types, lifting) place.disc(4))
        then have not_in: "place_side (edge_from e') \<noteq> In"
          using side_eq by metis
        moreover have not_out: "place_side (edge_from e') \<noteq> Out"
          using R(1) edge_in_flowI(2) op y.edge_from_open by force
        moreover have "edge_from e = shiftOpenPlace (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (edge_from e')"
          using from_eq not_in not_out op
          by (clarsimp simp add: place_open_def shiftPort_def)
        ultimately have "edge_from e
          \<in> set (map (shiftOpenPlace (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x))))
                  (filter (\<lambda>x. place_open x \<and> place_side x \<noteq> In \<and> place_side x \<noteq> Out) (pgraphPlaces y)))"
          unfolding set_map set_filter
          using imageI mem_Collect_eq by blast
        then show ?thesis
          unfolding pgraphPlaces_seqPortGraphs set_append by blast
      qed
    qed

    from assms(1,2) e show "edge_to e \<in> set (pgraphPlaces (seqPortGraphs x y))"
    proof (cases rule: seqPortGraphs_edge_cases)
      case Stitch
      then show ?thesis
      proof (cases "edge_to e")
        case (GroundPort qp)
        then have "edge_to e \<in> set (filter (\<lambda>x. place_ground x) (pgraphPlaces y))"
          using Stitch y.edge_to_pg by (fastforce elim!: seqInterfaceEdges_setD)
        then show ?thesis
          by (fastforce simp add: pgraphPlaces_seqPortGraphs)
      next
        case (OpenPort p)
        then have "edge_to e \<in> set (filter (\<lambda>x. place_open x \<and> place_side x = Out) (pgraphPlaces y))"
          using Stitch y.edge_to_pg y.edge_to_open seqInterfaceEdges_to_ex_edge
          by (metis (mono_tags, lifting) mem_Collect_eq place.disc(4) set_filter)
        then show ?thesis
          by (fastforce simp add: pgraphPlaces_seqPortGraphs)
      qed
    next
      case L
      then show ?thesis
      proof (cases "edge_to e")
        case (GroundPort qp)
        then show ?thesis
          using L x.edge_to_pg pgraphPlaces_seqPortGraphs
          by (metis (no_types, lifting) Un_iff filter_set member_filter place.disc(1) set_append)
      next
        case (OpenPort p)
        moreover have "place_side (edge_to e) \<noteq> Out"
          using L OpenPort by (simp add: toOpenOut_def)
        ultimately show ?thesis
          using L x.edge_to_pg pgraphPlaces_seqPortGraphs
          by (metis (mono_tags, lifting) Un_iff filter_set member_filter place.disc(4) set_append)
      qed
    next
      case (R e')
      then show ?thesis
      proof (cases "edge_to e")
        case (GroundPort qp)
        moreover have "edge_to e = edge_to e'"
          using R(3) GroundPort
          by (metis (no_types, lifting) place.disc(1) shiftOpenInEdge_simps(2) shiftOpenPlace_ground)
        ultimately show ?thesis
          using R y.edge_to_pg pgraphPlaces_seqPortGraphs
          by (metis (no_types, lifting) Un_iff filter_set member_filter place.disc(1) set_append)
      next
        case (OpenPort p)

        have to_eq: "edge_to e = shiftOpenPlace (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (edge_to e')"
          using R(3) OpenPort shiftOpenInEdge_simps(2) by blast
        have side_eq: "place_side (edge_to e) = place_side (edge_to e')"
          using to_eq by (metis (no_types, lifting) shiftOpenPlace_side)

        have in_y: "edge_to e' \<in> set (pgraphPlaces y)"
          using R(1) y.edge_to_pg by metis
        have op: "place_open (edge_to e')"
          using to_eq OpenPort shiftOpenPlace_open(1) by (metis (no_types, lifting) place_open_def)
        have not_in: "place_side (edge_to e') \<noteq> In"
          by (metis R(1) edge_in_flowI(3) in_out_distinct op y.edge_to_open)

        have "edge_to e \<in> set (filter (\<lambda>x. place_open x \<and> place_side x = Out) (pgraphPlaces y))"
          if "place_side (edge_to e) = Out"
        proof -
          have "edge_to e = edge_to e'"
            using that to_eq op by (clarsimp simp add: shiftPort_def place_open_def) (metis port.collapse)
          then show ?thesis
            using in_y that op by fastforce
        qed
        moreover have "edge_to e
          \<in> set (map (shiftOpenPlace (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x))))
                  (filter (\<lambda>x. place_open x \<and> place_side x \<noteq> In \<and> place_side x \<noteq> Out) (pgraphPlaces y)))"
          if "place_side (edge_to e) \<noteq> Out"
        proof -
          have not_out: "place_side (edge_to e') \<noteq> Out"
            using that side_eq by metis
          moreover have "edge_to e = shiftOpenPlace (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (edge_to e')"
            using to_eq not_in not_out op
            by (clarsimp simp add: place_open_def shiftPort_def)
          ultimately show ?thesis
            using in_y op not_in
            unfolding set_map set_filter
            using imageI mem_Collect_eq by blast
        qed
        ultimately show ?thesis
          unfolding pgraphPlaces_seqPortGraphs set_append by blast
      qed
    qed
  next
    fix m n
    assume "m \<in> set (pg_nodes (seqPortGraphs x y))"
       and "n \<in> set (pg_nodes (seqPortGraphs x y))"
       and "node_name m = node_name n"
    then show "m = n"
      using assms x.node_unique_path y.node_unique_path by fastforce
  next
    fix p
    assume p: "p \<in> set (pg_ports (seqPortGraphs x y))"
    then consider
        (X) "p \<in> set (pg_ports x)" and "port.side p \<noteq> Out"
      | (Y_Out) "p \<in> set (pg_ports y)" and "port.side p = Out"
      | (Y) p' where "p = shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x))) p'"
        and "p' \<in> set (pg_ports y)" and "port.side p' \<noteq> In" and "port.side p' \<noteq> Out"
      by simp blast
    then show "port.index p < length (filter (\<lambda>x. port.side x = port.side p) (pg_ports (seqPortGraphs x y)))"
    proof cases
      case X
      then show ?thesis
        using x.ports_index_bound by simp (metis (mono_tags, lifting) filter_cong trans_less_add1)
    next
      case Y_Out
      then show ?thesis
        using y.ports_index_bound by simp (metis (mono_tags, lifting) filter_cong)
    next
      case Y
      moreover have
        " (port.side x \<noteq> Out \<and> port.side x = port.side p')
        = (port.side x = port.side p')"
        for x :: "('s, 'a) port"
        using Y(4) by fastforce
      moreover have
        " (port.side x \<noteq> In \<and> port.side x = port.side p')
        = (port.side x = port.side p')"
        for x :: "('s, 'a) port"
        using Y(3) by fastforce
      ultimately show ?thesis
        using y.ports_index_bound by simp
    qed
  next
    fix p q
    assume "p \<in> set (pg_ports (seqPortGraphs x y))"
       and "q \<in> set (pg_ports (seqPortGraphs x y))"
       and side_eq: "port.side p = port.side q"
       and index_eq: "port.index p = port.index q"
    then consider
        (XX) "p \<in> set (pg_ports x)" and "port.side p \<noteq> Out"
        and "q \<in> set (pg_ports x)" and "port.side q \<noteq> Out"
      | (XY) q' where "p \<in> set (pg_ports x)" and "port.side p \<noteq> Out"
        and "q = shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x))) q'"
        and "q' \<in> set (pg_ports y)" and "port.side q' \<noteq> In" and "port.side q' \<noteq> Out"
      | (YY_Out) "p \<in> set (pg_ports y)" and "port.side p = Out"
        and "q \<in> set (pg_ports y)" and "port.side q = Out"
      | (YX) p' where "p = shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x))) p'"
        and "p' \<in> set (pg_ports y)" and "port.side p' \<noteq> In" and "port.side p' \<noteq> Out"
        and "q \<in> set (pg_ports x)" and "port.side q \<noteq> Out"
      | (YY) p' q' where "p = shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x))) p'"
        and "p' \<in> set (pg_ports y)" and "port.side p' \<noteq> In" and "port.side p' \<noteq> Out"
        and "q = shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x))) q'"
        and "q' \<in> set (pg_ports y)" and "port.side q' \<noteq> In" and "port.side q' \<noteq> Out"
      by simp (smt (verit, ccfv_SIG) image_iff mem_Collect_eq shiftPort_simps(2))
    then show "port.label p = port.label q"
    proof cases
      case XX
      then show ?thesis using x.open_ports_label_eq side_eq index_eq by metis
    next
      case XY
      then have False
        using index_eq side_eq x.ports_index_bound by fastforce
      then show ?thesis ..
    next
      case YY_Out
      then show ?thesis using y.open_ports_label_eq side_eq index_eq by metis
    next
      case YX
      then have False
        using index_eq side_eq x.ports_index_bound by fastforce
      then show ?thesis ..
    next
      case YY
      then show ?thesis
        using index_eq side_eq y.open_ports_label_eq
        by (metis add_left_cancel shiftPort_simps(2,3,4))
    qed
  next
    fix n p q
    assume "n \<in> set (pg_nodes (seqPortGraphs x y))"
       and "p \<in> set (node_ports n)"
       and "q \<in> set (node_ports n)"
       and "port.side p = port.side q"
       and "port.index p = port.index q"
    then show "port.label p = port.label q"
      by (metis in_nodes_seqPortGraphsE x.node_ports_label_eq y.node_ports_label_eq)
  next
    have "set (pg_nodes x) \<inter> set (pg_nodes y) = {}"
      using assms(3) by blast
    then show "distinct (pg_nodes (seqPortGraphs x y))"
      using assms x.nodes_distinct y.nodes_distinct by simp

    show "distinct (pg_edges (seqPortGraphs x y))"
    proof -
      have False
        if " shiftOpenInEdge
              (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
              (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))) e
           \<in> set (pg_edges x)" (is "?shifted \<in> set (pg_edges x)")
       and "\<not> toOpenOut e" and "e \<in> set (pg_edges y)" and "\<not> fromOpenIn e"
       for e
      proof (cases "place_ground (edge_from e) \<and> place_ground (edge_to e)")
        case True
        then show ?thesis
          using that(1,3) assms(3) x.edge_from_pg y.edge_from_pg
          by (metis (no_types, lifting) place.distinct_disc(1) place_in_pg_disjoint shiftOpenInEdge_simps(1) shiftOpenPlace_ground(2))
      next
        case False
        then consider "place_open (edge_from e)" | "place_open (edge_to e)"
          by fastforce
        then show ?thesis
        proof cases
          case 1
          moreover have "shiftOpenPlace (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (edge_from e) \<in> set (pgraphPlaces x)"
            using that(1) x.edge_from_pg by fastforce
          then have "shiftPort (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (place_port (edge_from e)) \<in> set (pg_ports x)"
            using 1 x.open_port_pg by (metis (no_types, lifting) shiftOpenPlace_open)
          moreover have "place_side (edge_from e) \<noteq> In"
            using that(4) 1 by blast
          moreover have "place_side (edge_from e) \<noteq> Out"
            using 1 edge_in_flowI(2) that(3) y.edge_from_open by (metis in_out_distinct)
          ultimately have "shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (place_port (edge_from e)) \<in> set (pg_ports x)"
            by (simp add: shiftPort_def)
          then have
            " port.index (shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (place_port (edge_from e)))
            < length (filter (\<lambda>x. port.side x = place_side (edge_from e)) (pg_ports x))"
            using x.ports_index_bound by (metis place_side.elims shiftPort_simps(2))
          moreover have
            " port.index (shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (place_port (edge_from e)))
            \<ge> length (filter (\<lambda>x. port.side x = place_side (edge_from e)) (pg_ports x))"
            by simp
          ultimately show False
            by simp
        next
          case 2
          moreover have "shiftOpenPlace (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (edge_to e) \<in> set (pgraphPlaces x)"
            using that(1) x.edge_to_pg by fastforce
          then have "shiftPort (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (place_port (edge_to e)) \<in> set (pg_ports x)"
            using 2 x.open_port_pg by (metis (no_types, lifting) shiftOpenPlace_open)
          moreover have "place_side (edge_to e) \<noteq> Out"
            using that(2) 2 by blast
          moreover have "place_side (edge_to e) \<noteq> In"
            using 2 edge_in_flowI(3) that(3) y.edge_to_open by (metis in_out_distinct)
          ultimately have "shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (place_port (edge_to e)) \<in> set (pg_ports x)"
            by (simp add: shiftPort_def)
          then have
            " port.index (shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (place_port (edge_to e)))
            < length (filter (\<lambda>x. port.side x = place_side (edge_to e)) (pg_ports x))"
            using x.ports_index_bound by (metis place_side.elims shiftPort_simps(2))
          moreover have
            " port.index (shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (place_port (edge_to e)))
            \<ge> length (filter (\<lambda>x. port.side x = place_side (edge_to e)) (pg_ports x))"
            by simp
          ultimately show False
            by simp
        qed
      qed
      then have
        " set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x))
        \<inter> set (map (shiftOpenInEdge
                 (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
                 (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))))
                (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y)))
        = {}"
        by (clarsimp simp add: disjoint_iff) blast
      moreover have
        " set (seqInterfaceEdges x y) \<inter>
          set ( filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x)
              @ map (shiftOpenInEdge
                       (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
                       (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))))
                  (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y))) =
          {}"
      proof -
        have "set (seqInterfaceEdges x y) \<inter> set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x)) = {}"
          unfolding disjoint_iff_not_equal toOpenOut_def
          using assms(3) y.edge_to_pg y.edge_to_open x.edge_to_pg
          by (smt (verit, best) filter_set member_filter place_in_pg_disjoint seqInterfaceEdges_setD)
        moreover have
          " set (seqInterfaceEdges x y)
          \<inter> set (map (shiftOpenInEdge
                       (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
                       (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))))
                  (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y)))
           = {}"
          unfolding disjoint_iff_not_equal fromOpenIn_def
          using assms(3) x.edge_from_open x.edge_from_pg y.edge_from_pg
          by (smt (verit) filter_set image_iff image_set member_filter not_place_open place_in_pg_disjoint seqInterfaceEdges_setD
              shiftOpenInEdge_simps(1) shiftOpenPlace_ground(2) shiftOpenPlace_open(1) shiftOpenPlace_side)
        ultimately show ?thesis
          unfolding set_append Int_Un_distrib Un_empty by (rule conjI)
      qed
      moreover have "distinct (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x))"
        using x.edges_distinct by force
      moreover have "distinct (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y))"
        using y.edges_distinct by force
      then have "distinct (map (shiftOpenInEdge
                    (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
                    (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))))
                  (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y)))"
        using distinct_map inj_shiftOpenInEdge inj_on_subset by blast
      moreover have "distinct (seqInterfaceEdges x y)"
        using distinct_seqInterfaceEdges by blast
      ultimately show ?thesis
        using assms(1,2) seqPortGraphs_flow_edges distinct_append by (metis (lifting) ext)
    qed

    show "distinct (pg_ports (seqPortGraphs x y))"
      using x.ports_distinct y.ports_distinct x.ports_index_bound
      using inj_shiftPort subset_UNIV inj_on_subset
      by (fastforce simp add: inf_set_def distinct_map)
  next
    fix e
    note assms(1,2)
    moreover assume "e \<in> set (pg_edges (seqPortGraphs x y))"
       and e_from: "place_open (edge_from e)"
       and flow: "edge_in_flow e"
    ultimately show "place_side (edge_from e) = In"
    proof (cases rule: seqPortGraphs_edge_cases)
      case Stitch
      then show ?thesis
        using e_from x.edge_from_open y.edge_from_open by (metis seqInterfaceEdges_from_ex_edge)
    next case L then show ?thesis using e_from flow x.edge_from_open by blast
    next case (R e') then show ?thesis using e_from flow y.edge_from_open by simp
    qed
  next
    fix e
    note assms(1,2)
    moreover assume "e \<in> set (pg_edges (seqPortGraphs x y))"
       and e_to: "place_open (edge_to e)"
       and flow: "edge_in_flow e"
    ultimately show "place_side (edge_to e) = Out"
    proof (cases rule: seqPortGraphs_edge_cases)
      case Stitch
      then show ?thesis
        using e_to x.edge_to_open y.edge_to_open by (metis seqInterfaceEdges_to_ex_edge)
    next case L then show ?thesis using e_to flow x.edge_to_open by blast
    next case (R e') then show ?thesis using e_to flow y.edge_to_open by simp
    qed
  next
    fix e
    note assms(1,2)
    moreover assume "e \<in> set (pg_edges (seqPortGraphs x y))"
       and e_from: "place_ground (edge_from e)"
       and flow: "edge_in_flow e"
    ultimately show "place_side (edge_from e) = Out"
    proof (cases rule: seqPortGraphs_edge_cases)
      case Stitch
      then show ?thesis
        using e_from x.edge_from_ground y.edge_from_ground by (metis seqInterfaceEdges_from_ex_edge)
    next case L then show ?thesis using e_from flow x.edge_from_ground by blast
    next case (R e') then show ?thesis using e_from flow y.edge_from_ground by simp
    qed
  next
    fix e
    note assms(1,2)
    moreover assume "e \<in> set (pg_edges (seqPortGraphs x y))"
       and e_to: "place_ground (edge_to e)"
       and flow: "edge_in_flow e"
    ultimately show "place_side (edge_to e) = In"
    proof (cases rule: seqPortGraphs_edge_cases)
      case Stitch
      then show ?thesis
        using e_to x.edge_to_ground y.edge_to_ground by (metis seqInterfaceEdges_to_ex_edge)
    next case L then show ?thesis using e_to flow x.edge_to_ground by blast
    next case (R e') then show ?thesis using e_to flow y.edge_to_ground by simp
    qed
  qed
qed

subsection\<open>Associativity\<close>

text\<open>
  Shifting flow places by amount only non-zero for non-flow places (as in @{const seqPortGraphs})
  does noting to them.
\<close>
lemma shiftOpenPlace_out [simp]:
    fixes p :: "('s :: side_in_out, 'a, 'p) place" and N :: "'s \<Rightarrow> nat"
  assumes "place_side p = Out"
    shows "shiftOpenPlace (\<lambda>s. if s = In \<or> s = Out then 0 else N s) p = p"
proof (cases p)
  case (GroundPort qp)
  then show ?thesis by simp
next
  case (OpenPort p')
  then show ?thesis using assms by (cases p') simp
qed
lemma shiftOpenPlace_in [simp]:
    fixes p :: "('s :: side_in_out, 'a, 'p) place" and N :: "'s \<Rightarrow> nat"
  assumes "place_side p = In"
    shows "shiftOpenPlace (\<lambda>s. if s = In \<or> s = Out then 0 else N s) p = p"
proof (cases p)
  case (GroundPort qp)
  then show ?thesis by simp
next
  case (OpenPort p')
  then show ?thesis using assms by (cases p') simp
qed

text\<open>Set image commutes if the functions commute on that set.\<close>
lemma image_comm: (* TODO general theorem *)
  assumes "\<And>x. x \<in> A \<Longrightarrow> f (g x) = g (f x)"
    shows "f ` g ` A = g ` f ` A"
  using assms by (metis (mono_tags, lifting) image_comp image_cong o_apply)

text\<open>
  Sequential composition of port graphs is associative up to their equivalence assuming they are
  all port graphs with flow and none of their node names clash.
\<close>
(* A lot of this replicates the relevant Par proof, opportunity for extracting general facts? *)
lemma seqPortGraphs_assoc_pgEquiv:
  fixes x y z :: "('s :: side_in_out, 'a, 'p, 'l) port_graph"
  assumes "port_graph_flow x"
      and "port_graph_flow y"
      and "port_graph_flow z"
      and "pg_disjoint x y"
      and "pg_disjoint y z"
      and "pg_disjoint x z"
      and "port_graph_flow x'"
      and "port_graph_flow y'"
      and "port_graph_flow z'"
      and "pg_disjoint x' y'"
      and "pg_disjoint y' z'"
      and "pg_disjoint x' z'"
      and "x \<approx> x'"
      and "y \<approx> y'"
      and "z \<approx> z'"
    shows "seqPortGraphs (seqPortGraphs x y) z \<approx> seqPortGraphs x' (seqPortGraphs y' z')"
proof (rule pgEquivI_ex)
  interpret x: port_graph_flow x using assms by simp
  interpret y: port_graph_flow y using assms by simp
  interpret z: port_graph_flow z using assms by simp
  interpret x': port_graph_flow x' using assms by simp
  interpret y': port_graph_flow y' using assms by simp
  interpret z': port_graph_flow z' using assms by simp

  have "port_graph_flow (seqPortGraphs x y)"
    using assms port_graph_flow_seqPortGraphs by metis
  then interpret xy: port_graph_flow "seqPortGraphs x y" .
  have "port_graph_flow (seqPortGraphs x' y')"
    using assms port_graph_flow_seqPortGraphs by metis
  then interpret x'y': port_graph_flow "seqPortGraphs x' y'" .

  have "port_graph_flow (seqPortGraphs (seqPortGraphs x y) z)"
    using assms pg_disjoint_seqPortGraphs(1) port_graph_flow_seqPortGraphs by metis
  then show "port_graph (seqPortGraphs (seqPortGraphs x y) z)"
    by (rule port_graph_flow.axioms(1))
  have "port_graph_flow (seqPortGraphs x' (seqPortGraphs y' z'))"
    using assms pg_disjoint_seqPortGraphs(2) port_graph_flow_seqPortGraphs by metis
  then show "port_graph (seqPortGraphs x' (seqPortGraphs y' z'))"
    by (rule port_graph_flow.axioms(1))

  note pg_x = x.port_graph_axioms
  moreover note pg_x' = x'.port_graph_axioms
  ultimately obtain f_x g_x
    where "renameNode f_x ` (set (pg_nodes x)) = set (pg_nodes x')"
      and "set (pg_nodes x) = renameNode g_x ` (set (pg_nodes x'))"
      and "renameEdge f_x ` (set (pg_edges x)) = set (pg_edges x')"
      and "set (pg_edges x) = renameEdge g_x ` (set (pg_edges x'))"
      and "set (pg_ports x) = set (pg_ports x')"
      and "\<And>l. l \<in> node_name ` set (pg_nodes x) \<Longrightarrow> g_x (f_x l) = l"
      and "\<And>l. l \<in> node_name ` set (pg_nodes x') \<Longrightarrow> f_x (g_x l) = l"
    using assms(13) by (elim pgEquivE pgEquiv_witnessE) metis+
  note xx' = this

  note pg_y = y.port_graph_axioms
  moreover note pg_y' = y'.port_graph_axioms
  ultimately obtain f_y g_y
    where "renameNode f_y ` (set (pg_nodes y)) = set (pg_nodes y')"
      and "set (pg_nodes y) = renameNode g_y ` (set (pg_nodes y'))"
      and "renameEdge f_y ` (set (pg_edges y)) = set (pg_edges y')"
      and "set (pg_edges y) = renameEdge g_y ` (set (pg_edges y'))"
      and "set (pg_ports y) = set (pg_ports y')"
      and "\<And>l. l \<in> node_name ` set (pg_nodes y) \<Longrightarrow> g_y (f_y l) = l"
      and "\<And>l. l \<in> node_name ` set (pg_nodes y') \<Longrightarrow> f_y (g_y l) = l"
    using assms(14) by (elim pgEquivE pgEquiv_witnessE) metis+
  note yy' = this

  note pg_z = z.port_graph_axioms
  moreover note pg_z' = z'.port_graph_axioms
  ultimately obtain f_z g_z
    where "renameNode f_z ` (set (pg_nodes z)) = set (pg_nodes z')"
      and "set (pg_nodes z) = renameNode g_z ` (set (pg_nodes z'))"
      and "renameEdge f_z ` (set (pg_edges z)) = set (pg_edges z')"
      and "set (pg_edges z) = renameEdge g_z ` (set (pg_edges z'))"
      and "set (pg_ports z) = set (pg_ports z')"
      and "\<And>l. l \<in> node_name ` set (pg_nodes z) \<Longrightarrow> g_z (f_z l) = l"
      and "\<And>l. l \<in> node_name ` set (pg_nodes z') \<Longrightarrow> f_z (g_z l) = l"
    using assms(15) by (elim pgEquivE pgEquiv_witnessE) metis+
  note zz' = this

  have len_fil_x: "length (filter P (pg_ports x)) = length (filter P (pg_ports x'))" for P
    using xx'(5) x.ports_distinct x'.ports_distinct
    by (metis distinct_length_filter)
  have len_fil_y: "length (filter P (pg_ports y)) = length (filter P (pg_ports y'))" for P
    using yy'(5) y.ports_distinct y'.ports_distinct
    by (metis distinct_length_filter)
  have "set (pg_ports (seqPortGraphs x y)) = set (pg_ports (seqPortGraphs x' y'))"
    by (simp add: xx'(5) yy'(5) len_fil_x)
  then have len_fil_xy: "length (filter P (pg_ports (seqPortGraphs x y))) = length (filter P (pg_ports (seqPortGraphs x' y')))" for P
    using xy.ports_distinct x'y'.ports_distinct
    by (metis distinct_length_filter)

  have
    " shiftPort
        (\<lambda>s. length (filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = s) (pg_ports x')) +
            (length (filter (\<lambda>x. port.side x = Out \<and> port.side x = s) (pg_ports y')) +
             length (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = s) (pg_ports y')))) p
    = shiftPort
        (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x')) +
             length (filter (\<lambda>p. port.side p = s) (pg_ports y'))) p"
    if "port.side p \<noteq> In" and "port.side p \<noteq> Out"
    for p :: "('s, 'a) port"
    \<comment> \<open>For a non-flow port, shifting it by number of same-side ports counted with flow precautions
        is the same as without those precautions. This plays a role in shifting ports of @{term z'}.\<close>
  proof -
    have
      " filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = port.side p) xs
      = filter (\<lambda>x. port.side x = port.side p) xs"
      for xs :: "('s, 'a) port list"
      using that(2) by metis
    moreover have "filter (\<lambda>x. port.side x = Out \<and> port.side x = port.side p) xs  = []"
      for xs :: "('s, 'a) port list"
      using that(2) by simp
    moreover have
      " filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = port.side p) xs
      = filter (\<lambda>x. port.side x = port.side p) xs"
      for xs :: "('s, 'a) port list"
      using that by metis
    ultimately show ?thesis
      by (simp add: shiftPort_def)
  qed
  then show
    " set (pg_ports (seqPortGraphs (seqPortGraphs x y) z))
    = set (pg_ports (seqPortGraphs x' (seqPortGraphs y' z')))"
    by (simp add: xx'(5) yy'(5) zz'(5) len_fil_x len_fil_y) blast

  let ?f = "\<lambda>p.
    if p \<in> set (map node_name (pg_nodes x))
      then f_x p
      else if p \<in> set (map node_name (pg_nodes y))
        then f_y p
        else if p \<in> set (map node_name (pg_nodes z))
          then f_z p
          else undefined"

  (* TODO I wish there was a command to assign a list of theorems in sequence to a list of names *)
  note thm_buffer = pgEquiv_witness_combine_3[OF pg_x pg_y pg_z assms(4,5,6), where f_x = f_x and f_y = f_y and f_z = f_z]
  note renameNode_f_x = thm_buffer(1)
  note renameNode_f_y = thm_buffer(2)
  note renameNode_f_z = thm_buffer(3)
  note renameEdge_f_x = thm_buffer(7)
  note renameEdge_f_y = thm_buffer(8)
  note renameEdge_f_z = thm_buffer(9)

  let ?g = "\<lambda>p.
    if p \<in> set (map node_name (pg_nodes x'))
      then g_x p
      else if p \<in> set (map node_name (pg_nodes y'))
        then g_y p
        else if p \<in> set (map node_name (pg_nodes z'))
          then g_z p
          else undefined"

  (* TODO I wish there was a command to assign a list of theorems in sequence to a list of names *)
  note thm_buffer = pgEquiv_witness_combine_3[OF pg_x' pg_y' pg_z' assms(10,11,12), where f_x = g_x and f_y = g_y and f_z = g_z]
  note renameNode_g_x = thm_buffer(1)
  note renameNode_g_y = thm_buffer(2)
  note renameNode_g_z = thm_buffer(3)
  note renameEdge_g_x = thm_buffer(7)
  note renameEdge_g_y = thm_buffer(8)
  note renameEdge_g_z = thm_buffer(9)

  have inv_on_places_x:
    "renamePlace ?g (renamePlace ?f p) = p" if p_in: "p \<in> set (pgraphPlaces x)" for p
  proof (cases p)
    case (GroundPort qp)
    then obtain n p'
      where "n \<in> set (pg_nodes x)" and "p' \<in> set (node_ports n)"
        and p: "p = GroundPort (QPort p' (node_name n))"
      using GroundPort p_in by fastforce
    then show ?thesis
      by (simp add: xx'(6)) (metis xx'(1) imageI renameNode_simps(2))
  next case (OpenPort p') then show ?thesis by simp
  qed
  then have inv_on_edges_x:
    "e \<in> set (pg_edges x) \<Longrightarrow> renameEdge ?g (renameEdge ?f e) = e" for e
    by (rule x.inv_on_edges)

  have inv_on_places_y:
    "renamePlace ?g (renamePlace ?f p) = p" if p_in: "p \<in> set (pgraphPlaces y)" for p
  proof (cases p)
    case (GroundPort qp)
    then obtain n p'
      where n: "n \<in> set (pg_nodes y)" and "p' \<in> set (node_ports n)"
        and "p = GroundPort (QPort p' (node_name n))"
      using that p_in by fastforce
    moreover have "node_name n \<notin> node_name ` set (pg_nodes x)"
      using n assms(4) by fastforce
    ultimately show ?thesis
      using renameNode_g_y yy'(6)
      by simp (smt (z3) yy'(1) imageI renameNode_simps(2))
  next case (OpenPort p') then show ?thesis by simp
  qed
  then have inv_on_edges_y:
    "e \<in> set (pg_edges y) \<Longrightarrow> renameEdge ?g (renameEdge ?f e) = e" for e
    by (rule y.inv_on_edges)

  have inv_on_places_z:
    "renamePlace ?g (renamePlace ?f p) = p" if p_in: "p \<in> set (pgraphPlaces z)" for p
  proof (cases p)
    case (GroundPort qp)
    then obtain n p'
      where n: "n \<in> set (pg_nodes z)" and "p' \<in> set (node_ports n)"
        and "p = GroundPort (QPort p' (node_name n))"
      using that p_in by fastforce
    moreover have "node_name n \<notin> node_name ` set (pg_nodes x)"
      using n assms(6) by fastforce
    moreover have "node_name n \<notin> node_name ` set (pg_nodes y)"
      using n assms(5) by fastforce
    ultimately show ?thesis
      using renameNode_g_z zz'(6)
      by simp (smt (verit, best) image_eqI image_set renameNode_simps(2) zz'(1))
  next case (OpenPort p') then show ?thesis by simp
  qed
  then have inv_on_edges_z:
    "e \<in> set (pg_edges z) \<Longrightarrow> renameEdge ?g (renameEdge ?f e) = e" for e
    by (rule z.inv_on_edges)

  have inv_on_places_x':
    "renamePlace ?f (renamePlace ?g p) = p" if p_in: "p \<in> set (pgraphPlaces x')" for p
  proof (cases p)
    case (GroundPort qp)
    then obtain n p'
      where "n \<in> set (pg_nodes x')" and "p' \<in> set (node_ports n)"
        and p: "p = GroundPort (QPort p' (node_name n))"
      using GroundPort p_in by fastforce
    then show ?thesis
      by (simp add: xx'(7)) (metis xx'(2) imageI renameNode_simps(2))
  next case (OpenPort p') then show ?thesis by simp
  qed
  then have inv_on_edges_x':
    "e \<in> set (pg_edges x') \<Longrightarrow> renameEdge ?f (renameEdge ?g e) = e" for e
    by (rule x'.inv_on_edges)

  have inv_on_places_y':
    "renamePlace ?f (renamePlace ?g p) = p" if p_in: "p \<in> set (pgraphPlaces y')" for p
  proof (cases p)
    case (GroundPort qp)
    then obtain n p'
      where n: "n \<in> set (pg_nodes y')" and "p' \<in> set (node_ports n)"
        and "p = GroundPort (QPort p' (node_name n))"
      using that p_in by fastforce
    moreover have "node_name n \<notin> node_name ` set (pg_nodes x')"
      using n assms(10) by fastforce
    ultimately show ?thesis
      using renameNode_f_y yy'(7)
      by simp (smt (z3) yy'(2) imageI renameNode_simps(2))
  next case (OpenPort p') then show ?thesis by simp
  qed
  then have inv_on_edges_y':
    "e \<in> set (pg_edges y') \<Longrightarrow> renameEdge ?f (renameEdge ?g e) = e" for e
    by (rule y'.inv_on_edges)

  have inv_on_places_z':
    "renamePlace ?f (renamePlace ?g p) = p" if p_in: "p \<in> set (pgraphPlaces z')" for p
  proof (cases p)
    case (GroundPort qp)
    then obtain n p'
      where n: "n \<in> set (pg_nodes z')" and "p' \<in> set (node_ports n)"
        and "p = GroundPort (QPort p' (node_name n))"
      using that p_in by fastforce
    moreover have "node_name n \<notin> node_name ` set (pg_nodes x')"
      using n assms(12) by fastforce
    moreover have "node_name n \<notin> node_name ` set (pg_nodes y')"
      using n assms(11) by fastforce
    ultimately show ?thesis
      using renameNode_f_z zz'(7)
      by simp (smt (verit, best) image_eqI image_set renameNode_simps(2) zz'(2))
  next case (OpenPort p') then show ?thesis by simp
  qed
  then have inv_on_edges_z':
    "e \<in> set (pg_edges z') \<Longrightarrow> renameEdge ?f (renameEdge ?g e) = e" for e
    by (rule z'.inv_on_edges)

  \<comment> \<open>Set up shorthands for the many used edge/place shift amounts.\<close>
  let ?shiftX = "(\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))"
  let ?shiftX' = "(\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x')))"
  let ?shiftY = "(\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports y)))"
  let ?shiftY' = "(\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports y')))"
  let ?shiftXY = "(\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports (seqPortGraphs x y))))"

  have
    " renameNode ?f ` set (pg_nodes (seqPortGraphs (seqPortGraphs x y) z)) =
      set (pg_nodes (seqPortGraphs x' (seqPortGraphs y' z')))"
    \<comment> \<open>Prove connection between node sets separately for each port graph's nodes, then combine.\<close>
  proof -
    have "renameNode ?f ` set (pg_nodes x) = set (pg_nodes x')"
      using renameNode_f_x xx'(1) by simp
    moreover have "renameNode ?f ` set (pg_nodes y) = set (pg_nodes y')"
      using renameNode_f_y yy'(1) by simp
    moreover have "renameNode ?f ` set (pg_nodes z) = set (pg_nodes z')"
      using renameNode_f_z zz'(1) by simp
    ultimately show ?thesis
      by (simp add: image_Un)
  qed
  moreover have
    " set (pg_nodes (seqPortGraphs (seqPortGraphs x y) z)) =
      renameNode ?g ` set (pg_nodes (seqPortGraphs x' (seqPortGraphs y' z')))"
    \<comment> \<open>Prove connection between node sets separately for each port graph's nodes, then combine.\<close>
  proof -
    have "set (pg_nodes x) = renameNode ?g ` set (pg_nodes x')"
      using renameNode_g_x xx'(2) by simp
    moreover have "set (pg_nodes y) = renameNode ?g ` set (pg_nodes y')"
      using renameNode_g_y yy'(2) by simp
    moreover have "set (pg_nodes z) = renameNode ?g ` set (pg_nodes z')"
      using renameNode_g_z zz'(2) by simp
    ultimately show ?thesis
      by (simp add: image_Un)
  qed
  moreover have
    " renameEdge ?f ` set (pg_edges (seqPortGraphs (seqPortGraphs x y) z)) =
      set (pg_edges (seqPortGraphs x' (seqPortGraphs y' z')))"
    \<comment> \<open>Prove connection between edge sets by proving which of their parts connect and combining
        those facts together.\<close>
  proof -
    have
      " renameEdge ?f ` set (seqInterfaceEdges (seqPortGraphs x y) z) \<union>
        renameEdge ?f ` set (filter (\<lambda>x. \<not> toOpenOut x) (seqInterfaceEdges x y))
      = set (seqInterfaceEdges x' (seqPortGraphs y' z')) \<union>
        shiftOpenInEdge ?shiftX' ?shiftX' `
          set (filter (\<lambda>x. \<not> fromOpenIn x) (seqInterfaceEdges y' z'))"
      \<comment> \<open>Most complex are edges crossing the interfaces, which split into four cases.\<close>
    proof -
      have
        " renameEdge ?f e \<in> set (seqInterfaceEdges x' (seqPortGraphs y' z'))
        \<or> renameEdge ?f e \<in> shiftOpenInEdge ?shiftX' ?shiftX' ` set (filter (\<lambda>x. \<not> fromOpenIn x) (seqInterfaceEdges y' z'))"
        if e: "e \<in> set (seqInterfaceEdges (seqPortGraphs x y) z)"
        for e :: "('s, 'a, 'p) edge"
        \<comment> \<open>Edges crossing the interface of @{term "seqPortGraphs x y"} with @{term z} correspond to
            either an edge in the interface of @{term x'} with @{term "seqPortGraphs y' z'"} (i.e.\ 
            its start is the result of crossing the interface of @{term x} and @{term y}) or a
            shifted edge (non-input) edge from just the interface of @{term y'} and @{term z'}
            (i.e.\ its start is an edge of only @{term y}).
            The core of the proof is considering possible cases where the start of this edge could
            come from, eliminating contradicting cases and proving the renaming connection.\<close>
      proof -
        obtain a b and p :: "('s, 'a) port"
          where "edge_from e = edge_from a" and "a \<in> set (pg_edges (seqPortGraphs x y))"
            and "edge_to e = edge_to b" and "b \<in> set (pg_edges z)"
            and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
            and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
            and "port.side p = Out"
          using e(1) seqInterfaceEdges_setD by blast
        note abp = this
  
        show ?thesis
          using assms(1,2) abp(2)
        proof (cases rule: seqPortGraphs_edge_cases)
          case Stitch
          then obtain aa ba and pa :: "('s, 'a) port"
            where "edge_from a = edge_from aa" and "aa \<in> set (pg_edges x)"
              and "edge_to a = edge_to ba" and "ba \<in> set (pg_edges y)"
              and "edge_to aa = OpenPort (portSetSide Out pa)" and "edge_in_flow aa"
              and "edge_from ba = OpenPort (portSetSide In pa)" and "edge_in_flow ba"
              and "port.side pa = Out"
            using seqInterfaceEdges_setD by blast
          note aa = this
    
          have "renameEdge ?f e \<in> set (seqInterfaceEdges x' (seqPortGraphs y' z'))"
          proof (rule seqInterfaceEdges_setI)
            show "port_graph_flow x'"
              using assms(7) .
            show "port_graph_flow (seqPortGraphs y' z')"
              using assms(8,9,11) by (rule port_graph_flow_seqPortGraphs)
            show "edge_from (renameEdge ?f e) = edge_from (renameEdge ?f aa)"
              using abp(1) aa(1) by simp
            show "renameEdge ?f aa \<in> set (pg_edges x')"
              using aa(2) renameEdge_f_x xx'(3) by blast
            show "edge_to (renameEdge ?f e) = edge_to (renameEdge ?f (Edge (edge_from ba) (edge_to b)))"
              using abp(3) by simp
            have "renameEdge ?f (Edge (edge_from ba) (edge_to b)) \<in> set (seqInterfaceEdges y' z')"
            proof (rule seqInterfaceEdges_setI)
              show "port_graph_flow y'"
                using assms(8) .
              show "port_graph_flow z'"
                using assms(9) .
              show "edge_from (renameEdge ?f (Edge (edge_from ba) (edge_to b))) = edge_from (renameEdge ?f ba)"
                by simp
              show "renameEdge ?f ba \<in> set (pg_edges y')"
                using aa(4) renameEdge_f_y yy'(3) by blast
              show "edge_to (renameEdge ?f (Edge (edge_from ba) (edge_to b))) = edge_to (renameEdge ?f b)"
                by simp
              show "renameEdge ?f b \<in> set (pg_edges z')"
                using abp(4) renameEdge_f_z zz'(3) by blast
              show "edge_to (renameEdge ?f ba) = OpenPort (portSetSide Out p)"
                using aa(3) abp(5) by (metis (no_types, lifting) renameEdge_simps(3) renamePlace.simps(2))
              show "edge_from (renameEdge ?f b) = OpenPort (portSetSide In p)"
                using abp(7) by simp
            qed
            then show "renameEdge ?f (Edge (edge_from ba) (edge_to b)) \<in> set (pg_edges (seqPortGraphs y' z'))"
              by simp
            show "edge_to (renameEdge ?f aa) = OpenPort (portSetSide Out pa)"
              using aa(5) by simp
            show "edge_from (renameEdge ?f (Edge (edge_from ba) (edge_to b))) = OpenPort (portSetSide In pa)"
              using aa(7) by simp
          qed
          then show ?thesis by blast
        next
          case L
          then show ?thesis using abp(5) by (simp add: toOpenOut_def)
        next
          case (R a')
  
          have "shiftOpenPlace ?shiftX' (edge_to b) = edge_to b"
            using abp(4,8) by (cases rule: z.edge_to_cases) simp_all
          then have "renameEdge ?f e = shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?f (Edge (edge_from a') (edge_to b)))"
            using R(3)[unfolded len_fil_x] abp(1,3) renameEdge_shiftOpenInEdge
            by (metis (no_types, lifting) edge.collapse edge.sel(1,2) shiftOpenInEdge_def)
          moreover have "renameEdge ?f (Edge (edge_from a') (edge_to b)) \<in> set (seqInterfaceEdges y' z')"
          proof (rule seqInterfaceEdges_setI)
              show "port_graph_flow y'"
                using assms(8) .
              show "port_graph_flow z'"
                using assms(9) .
              show "edge_from (renameEdge ?f (Edge (edge_from a') (edge_to b))) = edge_from (renameEdge ?f a')"
                by simp
              show "renameEdge ?f a' \<in> set (pg_edges y')"
                using R(1) renameEdge_f_y yy'(3) by blast
              show "edge_to (renameEdge ?f (Edge (edge_from a') (edge_to b))) = edge_to (renameEdge ?f b)"
                by simp
              show "renameEdge ?f b \<in> set (pg_edges z')"
                using abp(4) renameEdge_f_z zz'(3) by blast
              show "edge_to (renameEdge ?f a') = OpenPort (portSetSide Out p)"
              proof -
                have "shiftOpenPlace ?shiftX (edge_to a') = OpenPort (portSetSide Out p)"
                  using R(3) abp(5) by simp
                then have "renamePlace ?f (edge_to a') = OpenPort (portSetSide Out p)"
                  using abp(9) portSetSide_same shiftOpenPlace_out shiftOpenPlace_side
                  by (metis (no_types) place.disc(4) place_port.simps(2) place_side.simps renamePlace_simps(2))
                then show ?thesis
                  by simp
              qed
              show "edge_from (renameEdge ?f b) = OpenPort (portSetSide In p)"
                using abp(7) by simp
            qed
          moreover have "\<not> fromOpenIn (renameEdge ?f (Edge (edge_from a') (edge_to b)))"
            using R(2) by (simp add: fromOpenIn_def)
          ultimately show ?thesis
            by (smt (verit) image_eqI filter_set member_filter)
        qed
      qed
      moreover have "renameEdge ?f e \<in> set (seqInterfaceEdges x' (seqPortGraphs y' z'))"
        if e: "e \<in> set (seqInterfaceEdges x y)" "\<not> toOpenOut e"
        for e :: "('s, 'a, 'p) edge"
        \<comment> \<open>Non-output edges crossing the interface of @{term x} and @{term y} must correspond to an
            edge crossing the interface of @{term x'} and @{term "seqPortGraphs y' z'"}.
            The core of the proof is that, because the edge is non-output, we know its destination
            part must correspond to an edge of only @{term y'}.\<close>
      proof -
        obtain a b and p :: "('s, 'a) port"
          where "edge_from e = edge_from a" and "a \<in> set (pg_edges x)"
            and "edge_to e = edge_to b" and "b \<in> set (pg_edges y)"
            and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
            and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
            and "port.side p = Out"
          using e(1) seqInterfaceEdges_setD by blast
        note abp = this
    
        show ?thesis
        proof (rule seqInterfaceEdges_setI)
          show "port_graph_flow x'"
            using assms(7) .
          show "port_graph_flow (seqPortGraphs y' z')"
            using assms(8,9,11) by (rule port_graph_flow_seqPortGraphs)
          show "edge_from (renameEdge ?f e) = edge_from (renameEdge ?f a)"
            using abp(1) by simp
          show "renameEdge ?f a \<in> set (pg_edges x')"
            using abp(2) renameEdge_f_x xx'(3) by blast
          show "edge_to (renameEdge ?f e) = edge_to (renameEdge ?f b)"
            using abp(3) by simp
          have "renameEdge ?f b \<in> set (pg_edges y')"
            using abp(4) renameEdge_f_y yy'(3) by blast
          moreover have "\<not> toOpenOut b"
            using e(2) abp(3) by (simp add: toOpenOut_def)
          ultimately show "renameEdge ?f b \<in> set (pg_edges (seqPortGraphs y' z'))"
            using seqPortGraphs_flow_edges[OF assms(8,9)] by simp
          show "edge_to (renameEdge ?f a) = OpenPort (portSetSide Out p)"
            using abp(5) by simp
          show "edge_from (renameEdge ?f b) = OpenPort (portSetSide In p)"
            using abp(7) by simp
        qed
      qed
      moreover have
        " e \<in> renameEdge ?f ` set (seqInterfaceEdges (seqPortGraphs x y) z)
        \<or> e \<in> renameEdge ?f ` set (filter (\<lambda>x. \<not> toOpenOut x) (seqInterfaceEdges x y))"
        if e: "e \<in> set (seqInterfaceEdges x' (seqPortGraphs y' z'))"
        for e :: "('s, 'a, 'p) edge"
        \<comment> \<open>Edges crossing the interface of @{term x'} and @{term "seqPortGraphs y' z'"} correspond to
            either an edge in the interface of @{term "seqPortGraphs x y"} with @{term z} (i.e.\ 
            its end is the result of crossing the interface of @{term y'} and @{term z'}) or a
            non-output edge edge from just the interface of @{term x} and @{term y} (i.e.\ its end
            is an edge of only @{term y'}).
            The core of the proof is considering possible cases where the end of this edge could
            come from, eliminating contradicting cases and proving the renaming connection.\<close>
      proof -
        obtain a b and p :: "('s, 'a) port"
          where "edge_from e = edge_from a" and "a \<in> set (pg_edges x')"
            and "edge_to e = edge_to b" and "b \<in> set (pg_edges (seqPortGraphs y' z'))"
            and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
            and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
            and "port.side p = Out"
          using e(1) seqInterfaceEdges_setD by blast
        note abp = this
  
        show ?thesis
          using assms(8,9) abp(4)
        proof (cases rule: seqPortGraphs_edge_cases)
          case Stitch
          then obtain ba bb and pb :: "('s, 'a) port"
            where "edge_from b = edge_from ba" and "ba \<in> set (pg_edges y')"
              and "edge_to b = edge_to bb" and "bb \<in> set (pg_edges z')"
              and "edge_to ba = OpenPort (portSetSide Out pb)" and "edge_in_flow ba"
              and "edge_from bb = OpenPort (portSetSide In pb)" and "edge_in_flow bb"
              and "port.side pb = Out"
            using seqInterfaceEdges_setD by blast
          note bb = this
  
          have "e = renameEdge ?f (renameEdge ?g e)"
          proof -
            have "renamePlace ?f (renamePlace ?g (edge_from e)) = edge_from e"
              using abp(1,2) inv_on_places_x' x'.edge_from_pg by presburger
            moreover have "renamePlace ?f (renamePlace ?g (edge_to e)) = edge_to e"
              using abp(3) bb(3,4) inv_on_places_z' z'.edge_to_pg by presburger
            ultimately show ?thesis
              by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3))
          qed
          moreover have "renameEdge ?g e \<in> set (seqInterfaceEdges (seqPortGraphs x y) z)"
          proof (rule seqInterfaceEdges_setI)
            show "port_graph_flow (seqPortGraphs x y)"
              using assms(1,2,4) by (rule port_graph_flow_seqPortGraphs)
            show "port_graph_flow z"
              using assms(3) .
            show "edge_from (renameEdge ?g e) = edge_from (renameEdge ?g (Edge (edge_from a) (edge_to ba)))"
              using abp(1) by simp
            have "renameEdge ?g (Edge (edge_from a) (edge_to ba)) \<in> set (seqInterfaceEdges x y)"
            proof (rule seqInterfaceEdges_setI)
              show "port_graph_flow x"
                using assms(1) .
              show "port_graph_flow y"
                using assms(2) .
              show "edge_from (renameEdge ?g (Edge (edge_from a) (edge_to ba))) = edge_from (renameEdge ?g a)"
                using bb(1) by simp
              show "renameEdge ?g a \<in> set (pg_edges x)"
                using abp(2) renameEdge_g_x xx'(4) by blast
              show "edge_to (renameEdge ?g (Edge (edge_from a) (edge_to ba))) = edge_to (renameEdge ?g ba)"
                using bb(3) by simp
              show "renameEdge ?g ba \<in> set (pg_edges y)"
                using bb(2) renameEdge_g_y yy'(4) by blast
              show "edge_to (renameEdge ?g a) = OpenPort (portSetSide Out p)"
                using abp(5) by simp
              show "edge_from (renameEdge ?g ba) = OpenPort (portSetSide In p)"
                using bb(1) abp(7) by (metis (no_types, lifting) renameEdge_simps(2) renamePlace.simps(2))
            qed
            then show "renameEdge ?g (Edge (edge_from a) (edge_to ba)) \<in> set (pg_edges (seqPortGraphs x y))"
              by simp
            show "edge_to (renameEdge ?g e) = edge_to (renameEdge ?g bb)"
              using abp(3) bb(3) by simp
            show "renameEdge ?g bb \<in> set (pg_edges z)"
              using bb(4) renameEdge_g_z zz'(4) by blast
            show "edge_to (renameEdge ?g (Edge (edge_from a) (edge_to ba))) = OpenPort (portSetSide Out pb)"
              using bb(5) by simp
            show "edge_from (renameEdge ?g bb) = OpenPort (portSetSide In pb)"
              using bb(7) by simp
          qed
          ultimately have "e \<in> renameEdge ?f ` set (seqInterfaceEdges (seqPortGraphs x y) z)"
            by (rule image_eqI)
          then show ?thesis by blast
        next
          case L
  
          have "e = renameEdge ?f (renameEdge ?g e)"
          proof -
            have "renamePlace ?f (renamePlace ?g (edge_from e)) = edge_from e"
              using abp(1,2) inv_on_places_x' x'.edge_from_pg by presburger
            moreover have "renamePlace ?f (renamePlace ?g (edge_to e)) = edge_to e"
              using abp(3) L(1,2) inv_on_places_y' y'.edge_to_pg by presburger
            ultimately show ?thesis
              by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3))
          qed
          moreover have "renameEdge ?g e \<in> set (seqInterfaceEdges x y)"
          proof (rule seqInterfaceEdges_setI)
            show "port_graph_flow x"
              using assms(1) .
            show "port_graph_flow y"
              using assms(2) .
            show "edge_from (renameEdge ?g e) = edge_from (renameEdge ?g a)"
              using abp(1) by simp
            show "renameEdge ?g a \<in> set (pg_edges x)"
              using abp(2) renameEdge_g_x xx'(4) by blast
            show "edge_to (renameEdge ?g e) = edge_to (renameEdge ?g b)"
              using abp(3) by simp
            show "renameEdge ?g b \<in> set (pg_edges y)"
              using L(1) renameEdge_g_y yy'(4) by blast
            show "edge_to (renameEdge ?g a) = OpenPort (portSetSide Out p)"
              using abp(5) by simp
            show "edge_from (renameEdge ?g b) = OpenPort (portSetSide In p)"
              using abp(7) by simp
          qed
          moreover have "\<not> toOpenOut (renameEdge ?g e)"
            using L(2) abp(3) by (simp add: toOpenOut_def)
          ultimately have "e \<in> renameEdge ?f ` set (filter (\<lambda>x. \<not> toOpenOut x) (seqInterfaceEdges x y))"
            by (smt (verit) image_eqI filter_set member_filter)
          then show ?thesis by blast
        next
          case (R b')
          then have "\<not> fromOpenIn b"
            by simp
          then show ?thesis
            using abp(7) by (simp add: fromOpenIn_def)
        qed
      qed
      moreover have
        "shiftOpenInEdge ?shiftX' ?shiftX' e \<in> renameEdge ?f ` set (seqInterfaceEdges (seqPortGraphs x y) z)"
        if e: "e \<in> set (seqInterfaceEdges y' z')" "\<not> fromOpenIn e"
        for e :: "('s, 'a, 'p) edge"
        \<comment> \<open>Non-input edges crossing the interface of @{term y'} and @{term z'} must correspond to
            a shifted edge crossing the interface of @{term "seqPortGraphs x y"} and @{term z}.
            The core of the proof is that, because the edge is non-input, we know its start must
            come only from @{term y'} and thus correspond to an edge of @{term y}.\<close>
      proof -
        obtain a b and p :: "('s, 'a) port"
          where "edge_from e = edge_from a" and "a \<in> set (pg_edges y')"
            and "edge_to e = edge_to b" and "b \<in> set (pg_edges z')"
            and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
            and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
            and "port.side p = Out"
          using e(1) seqInterfaceEdges_setD by blast
        note abp = this

        let ?witness = "shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g (Edge (edge_from a) (edge_to b)))"
        have "shiftOpenInEdge ?shiftX' ?shiftX' e = renameEdge ?f ?witness"
        proof -
          have "edge_from a = renamePlace ?f (renamePlace ?g (edge_from a))"
            using abp(2) y'.edge_from_pg inv_on_places_y' by presburger
          moreover have "edge_to b = renamePlace ?f (renamePlace ?g (edge_to b))"
            using abp(4) z'.edge_to_pg inv_on_places_z' by presburger
          ultimately have "e = renameEdge ?f (renameEdge ?g (Edge (edge_from a) (edge_to b)))"
            using abp(1,3) by (smt (verit, ccfv_threshold) edge.collapse renameEdge_simps(1))
          then show ?thesis
            using renameEdge_shiftOpenInEdge by metis
        qed
        moreover have "?witness \<in> set (seqInterfaceEdges (seqPortGraphs x y) z)"
        proof (rule seqInterfaceEdges_setI)
          show "port_graph_flow (seqPortGraphs x y)"
            using assms(1,2,4) by (rule port_graph_flow_seqPortGraphs)
          show "port_graph_flow z"
            using assms(3) .

          have ga_in_y: "renameEdge ?g a \<in> set (pg_edges y)"
            using abp(2) renameEdge_g_y yy'(4) by blast

          have shift_a: "shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g a) = renameEdge ?g a"
          proof -
            have "place_side (edge_from (renameEdge ?g a)) = In \<or> place_side (edge_from (renameEdge ?g a)) = Out"
              using abp(6) ga_in_y y.edge_from_cases renameEdge_in_flow by blast
            then have "edge_from (shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g a)) = edge_from (renameEdge ?g a)"
              by fastforce
            moreover have "place_side (edge_to (renameEdge ?g a)) = Out"
              by (simp add: abp(5))
            then have "edge_to (shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g a)) = edge_to (renameEdge ?g a)"
              by fastforce
            ultimately show ?thesis
              using edge.expand by blast
          qed

          have "edge_from ?witness = edge_from (shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g a))"
            by simp
          then show "edge_from ?witness = edge_from (renameEdge ?g a)"
            using shift_a by metis

          have "\<not> fromOpenIn a"
            using e(2) abp(1) by (simp add: fromOpenIn_def)
          then have "shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g a) \<in> shiftOpenInEdge ?shiftX' ?shiftX' ` {x \<in> set (pg_edges y). \<not> fromOpenIn x}"
            using ga_in_y by simp
          then have "shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g a) \<in> set (pg_edges (seqPortGraphs x y))"
            by (unfold seqPortGraphs_flow_edges[OF assms(1,2)] set_append set_map len_fil_x set_filter)
               (intro UnI2)
          then show "renameEdge ?g a \<in> set (pg_edges (seqPortGraphs x y))"
            using shift_a by metis

          have "edge_to ?witness = edge_to (shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g b))"
            by simp
          moreover show "renameEdge ?g b \<in> set (pg_edges z)"
            using abp(4) renameEdge_g_z zz'(4) by blast
          then have "place_side (edge_to (renameEdge ?g b)) = In \<or> place_side (edge_to (renameEdge ?g b)) = Out"
            using abp(8) z.edge_to_cases renameEdge_in_flow by blast
          ultimately show "edge_to ?witness = edge_to (renameEdge ?g b)"
            by fastforce

          show "edge_to (renameEdge ?g a) = OpenPort (portSetSide Out p)"
            using abp(5) by simp
          show "edge_from (renameEdge ?g b) = OpenPort (portSetSide In p)"
            using abp(7) by simp
        qed
        ultimately show ?thesis by blast
      qed
      ultimately show ?thesis
        \<comment> \<open>Above four cases cover all combinations of the equality.\<close>
        by auto
    qed
    moreover have
      " renameEdge ?f ` set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x))
      = set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x'))"
      \<comment> \<open>Non-output edges of @{term x} are unchanged.\<close>
      using renameEdge_f_x xx'(3) by (fastforce simp del: not_place_open)
    moreover have
      " renameEdge ?f ` shiftOpenInEdge ?shiftX ?shiftX ` set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y))
      = shiftOpenInEdge ?shiftX' ?shiftX' ` set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y'))"
      \<comment> \<open>Non-flow edges of @{term y} are shifted by @{term x}'s.\<close>
    proof -
      have
        " renameEdge ?f ` set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y))
        = set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y'))"
        using renameEdge_f_y yy'(3) by (fastforce simp del: not_place_open)
      then have
        " renameEdge ?f ` shiftOpenInEdge ?shiftX ?shiftX ` set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y))
        = shiftOpenInEdge ?shiftX ?shiftX ` set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y'))"
        using renameEdge_shiftOpenInEdge by (metis (no_types, lifting) image_comm)
      then show ?thesis
        by (fold len_fil_x)
    qed
    moreover have
      " renameEdge ?f ` shiftOpenInEdge ?shiftXY ?shiftXY ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z))
      = shiftOpenInEdge ?shiftX' ?shiftX' ` shiftOpenInEdge ?shiftY' ?shiftY' ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z'))"
      \<comment> \<open>Non-input edges of @{term z} are shifted by both @{term x}'s and @{term y}'s.\<close>
    proof -
      have
        " renameEdge ?f ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z))
        = set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z'))"
        using renameEdge_f_z zz'(3) by (fastforce simp del: not_place_open)
      then have
        " renameEdge ?f ` shiftOpenInEdge ?shiftXY ?shiftXY ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z))
        = shiftOpenInEdge ?shiftXY ?shiftXY ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z'))"
        using renameEdge_shiftOpenInEdge by (metis (no_types, lifting) image_comm)
      moreover have "?shiftXY s = ?shiftX' s + ?shiftY' s" for s :: 's
        by (clarsimp simp add: len_fil_x len_fil_y) (smt (verit, del_insts) filter_cong)
      then have
        " shiftOpenInEdge ?shiftXY ?shiftXY ` A
        = shiftOpenInEdge ?shiftX' ?shiftX' ` shiftOpenInEdge ?shiftY' ?shiftY' ` A"
        for A :: "('s, 'a, 'p) edge set"
        by (simp add: image_comp)
      ultimately show ?thesis
        by metis
    qed
    ultimately have combined:
      " renameEdge ?f ` set (seqInterfaceEdges (seqPortGraphs x y) z) \<union>
        renameEdge ?f ` set (filter (\<lambda>x. \<not> toOpenOut x) (seqInterfaceEdges x y)) \<union>
        renameEdge ?f ` set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x)) \<union>
        renameEdge ?f `
          shiftOpenInEdge ?shiftX ?shiftX `
            set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y)) \<union>
        renameEdge ?f `
        shiftOpenInEdge ?shiftXY ?shiftXY ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z))
      = set (seqInterfaceEdges x' (seqPortGraphs y' z')) \<union>
        set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x')) \<union>
        shiftOpenInEdge ?shiftX' ?shiftX' `
          set (filter (\<lambda>x. \<not> fromOpenIn x) (seqInterfaceEdges y' z')) \<union>
        shiftOpenInEdge ?shiftX' ?shiftX' `
          set (filter (\<lambda>x. \<not> toOpenOut x \<and> \<not> fromOpenIn x) (pg_edges y')) \<union>
        shiftOpenInEdge ?shiftX' ?shiftX' `
          shiftOpenInEdge ?shiftY' ?shiftY' `
            set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z'))"
      \<comment> \<open>Gather these together into one statement about the edge sets.\<close>
      by (smt (verit) filter_cong sup_assoc sup_commute)

    have "port_graph_flow (seqPortGraphs y' z')"
      using assms(8,9,11) by (rule port_graph_flow_seqPortGraphs)
    moreover have "port_graph_flow (seqPortGraphs x y)"
      using assms(1,2,4) by (rule port_graph_flow_seqPortGraphs)
    ultimately show ?thesis
      \<comment> \<open>To complete, simplify the two levels of combinations on both sides,\<close>
      using x.port_graph_flow_axioms y.port_graph_flow_axioms z.port_graph_flow_axioms
      using x'.port_graph_flow_axioms y'.port_graph_flow_axioms z'.port_graph_flow_axioms
      apply (simp only: seqPortGraphs_flow_edges)
      \<comment> \<open>Simplify the result,\<close>
      unfolding set_append image_Un filter_map filter_append shiftOpenInEdge_toOpenOut filter_filter
        conj_absorb comp_def Un_assoc[symmetric] set_map[where f = "shiftOpenInEdge _ _"]
        shiftOpenInEdge_fromOpenIn
      \<comment> \<open>Apply the combined statement to the simplified goal.\<close>
      by (rule combined)
  qed
  moreover have
    " set (pg_edges (seqPortGraphs (seqPortGraphs x y) z)) =
      renameEdge ?g ` set (pg_edges (seqPortGraphs x' (seqPortGraphs y' z')))"
    \<comment> \<open>Prove connection between edge sets by proving which of their parts connect and combining
        those facts together.
        At the higher level the proof is similar to the previous, but care needs to be taken for the
        different placement of the renaming.\<close>
  proof -
    have
      " set (seqInterfaceEdges (seqPortGraphs x y) z)
      \<union> set (filter (\<lambda>x. \<not> toOpenOut x) (seqInterfaceEdges x y))
      = renameEdge ?g ` set (seqInterfaceEdges x' (seqPortGraphs y' z'))
      \<union> renameEdge ?g ` shiftOpenInEdge ?shiftX' ?shiftX' ` set (filter (\<lambda>x. \<not> fromOpenIn x) (seqInterfaceEdges y' z'))"
      \<comment> \<open>Most complex are edges crossing the interfaces, which split into four cases.\<close>
    proof -
      have
        " e \<in> renameEdge ?g ` set (seqInterfaceEdges x' (seqPortGraphs y' z'))
        \<or> e \<in> renameEdge ?g ` shiftOpenInEdge ?shiftX' ?shiftX' ` set (filter (\<lambda>x. \<not> fromOpenIn x) (seqInterfaceEdges y' z'))"
        if e: "e \<in> set (seqInterfaceEdges (seqPortGraphs x y) z)"
        for e :: "('s, 'a, 'p) edge"
        \<comment> \<open>Edges crossing the interface of @{term "seqPortGraphs x y"} with @{term z} correspond to
            either an edge in the interface of @{term x'} with @{term "seqPortGraphs y' z'"} (i.e.\ 
            its start is the result of crossing the interface of @{term x} and @{term y}) or a
            shifted edge (non-input) edge from just the interface of @{term y'} and @{term z'}
            (i.e.\ its start is an edge of only @{term y}).
            The core of the proof is considering possible cases where the start of this edge could
            come from, eliminating contradicting cases and proving the renaming connection.\<close>
      proof -
        obtain a b and p :: "('s, 'a) port"
          where "edge_from e = edge_from a" and "a \<in> set (pg_edges (seqPortGraphs x y))"
            and "edge_to e = edge_to b" and "b \<in> set (pg_edges z)"
            and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
            and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
            and "port.side p = Out"
          using e(1) seqInterfaceEdges_setD by blast
        note abp = this
  
        show ?thesis
          using assms(1,2) abp(2)
        proof (cases rule: seqPortGraphs_edge_cases)
          case Stitch
          then obtain aa ba and pa :: "('s, 'a) port"
            where "edge_from a = edge_from aa" and "aa \<in> set (pg_edges x)"
              and "edge_to a = edge_to ba" and "ba \<in> set (pg_edges y)"
              and "edge_to aa = OpenPort (portSetSide Out pa)" and "edge_in_flow aa"
              and "edge_from ba = OpenPort (portSetSide In pa)" and "edge_in_flow ba"
              and "port.side pa = Out"
            using seqInterfaceEdges_setD by blast
          note aa = this
  
          have "e = renameEdge ?g (renameEdge ?f e)"
          proof -
            have "renamePlace ?g (renamePlace ?f (edge_from e)) = edge_from e"
              using abp(1) aa(1,2) inv_on_places_x x.edge_from_pg by presburger
            moreover have "renamePlace ?g (renamePlace ?f (edge_to e)) = edge_to e"
              using abp(3,4) inv_on_places_z z.edge_to_pg by presburger
            ultimately show ?thesis
              by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3))
          qed
          moreover have "renameEdge ?f e \<in> set (seqInterfaceEdges x' (seqPortGraphs y' z'))"
          proof (rule seqInterfaceEdges_setI)
            show "port_graph_flow x'"
              using assms(7) .
            show "port_graph_flow (seqPortGraphs y' z')"
              using assms(8,9,11) by (rule port_graph_flow_seqPortGraphs)
            show "edge_from (renameEdge ?f e) = edge_from (renameEdge ?f aa)"
              using abp(1) aa(1) by simp
            show "renameEdge ?f aa \<in> set (pg_edges x')"
              using aa(2) renameEdge_f_x xx'(3) by blast
            show "edge_to (renameEdge ?f e) = edge_to (renameEdge ?f (Edge (edge_from ba) (edge_to b)))"
              using abp(3) by simp
            have "renameEdge ?f (Edge (edge_from ba) (edge_to b)) \<in> set (seqInterfaceEdges y' z')"
            proof (rule seqInterfaceEdges_setI)
              show "port_graph_flow y'"
                using assms(8) .
              show "port_graph_flow z'"
                using assms(9) .
              show "edge_from (renameEdge ?f (Edge (edge_from ba) (edge_to b))) = edge_from (renameEdge ?f ba)"
                by simp
              show "renameEdge ?f ba \<in> set (pg_edges y')"
                using aa(4) renameEdge_f_y yy'(3) by blast
              show "edge_to (renameEdge ?f (Edge (edge_from ba) (edge_to b))) = edge_to (renameEdge ?f b)"
                by simp
              show "renameEdge ?f b \<in> set (pg_edges z')"
                using abp(4) renameEdge_f_z zz'(3) by blast
              show "edge_to (renameEdge ?f ba) = OpenPort (portSetSide Out p)"
                using aa(3) abp(5) by (metis (no_types, lifting) renameEdge_simps(3) renamePlace.simps(2))
              show "edge_from (renameEdge ?f b) = OpenPort (portSetSide In p)"
                using abp(7) by simp
            qed
            then show "renameEdge ?f (Edge (edge_from ba) (edge_to b)) \<in> set (pg_edges (seqPortGraphs y' z'))"
              by simp
            show "edge_to (renameEdge ?f aa) = OpenPort (portSetSide Out pa)"
              using aa(5) by simp
            show "edge_from (renameEdge ?f (Edge (edge_from ba) (edge_to b))) = OpenPort (portSetSide In pa)"
              using aa(7) by simp
          qed
          ultimately show ?thesis by blast
        next
          case L
          then show ?thesis using abp(5) by (simp add: toOpenOut_def)
        next
          case (R a')

          let ?witness = "renameEdge ?f (Edge (edge_from a') (edge_to b))"
          have "e = renameEdge ?g (shiftOpenInEdge ?shiftX' ?shiftX' ?witness)"
          proof -
            have "edge_from e = edge_from (renameEdge ?g (shiftOpenInEdge ?shiftX' ?shiftX' ?witness))"
              using R abp(1,6) inv_on_edges_y y.edge_from_cases
              by (metis (no_types, lifting) edge.sel(1) fromOpenInI renameEdge_simps(2) renamePlace_simps(3) shiftOpenInEdge_in_flow
                  shiftOpenInEdge_simps(1) shiftOpenPlace_ground(2))
            moreover have "shiftOpenPlace ?shiftX' (edge_to b) = edge_to b"
              using abp(4,8) by (cases rule: z.edge_to_cases) simp_all
            then have "edge_to e = edge_to (renameEdge ?g (shiftOpenInEdge ?shiftX' ?shiftX' ?witness))"
              using R abp(3,4) inv_on_edges_z renamePlace_shiftOpenPlace
              by (metis (no_types, lifting) edge.sel(2) renameEdge_def shiftOpenInEdge_def)
            ultimately show ?thesis
              using edge.expand by blast
          qed
          moreover have "?witness \<in> set (seqInterfaceEdges y' z')"
          proof (rule seqInterfaceEdges_setI)
              show "port_graph_flow y'"
                using assms(8) .
              show "port_graph_flow z'"
                using assms(9) .
              show "edge_from ?witness = edge_from (renameEdge ?f a')"
                by simp
              show "renameEdge ?f a' \<in> set (pg_edges y')"
                using R(1) renameEdge_f_y yy'(3) by blast
              show "edge_to ?witness = edge_to (renameEdge ?f b)"
                by simp
              show "renameEdge ?f b \<in> set (pg_edges z')"
                using abp(4) renameEdge_f_z zz'(3) by blast
              show "edge_to (renameEdge ?f a') = OpenPort (portSetSide Out p)"
              proof -
                have "shiftOpenPlace ?shiftX (edge_to a') = OpenPort (portSetSide Out p)"
                  using R(3) abp(5) by simp
                then have "renamePlace ?f (edge_to a') = OpenPort (portSetSide Out p)"
                  using abp(9) portSetSide_same shiftOpenPlace_out shiftOpenPlace_side
                  by (metis (no_types) place.disc(4) place_port.simps(2) place_side.simps renamePlace_simps(2))
                then show ?thesis
                  by simp
              qed
              show "edge_from (renameEdge ?f b) = OpenPort (portSetSide In p)"
                using abp(7) by simp
            qed
          moreover have "\<not> fromOpenIn ?witness"
            using R(2) by (simp add: fromOpenIn_def)
          ultimately show ?thesis
            by (smt (verit) image_eqI filter_set member_filter)
        qed
      qed
      moreover have "e \<in> renameEdge ?g ` set (seqInterfaceEdges x' (seqPortGraphs y' z'))"
        if e: "e \<in> set (seqInterfaceEdges x y)" "\<not> toOpenOut e"
        for e :: "('s, 'a, 'p) edge"
        \<comment> \<open>Non-output edges crossing the interface of @{term x} and @{term y} must correspond to an
            edge crossing the interface of @{term x'} and @{term "seqPortGraphs y' z'"}.
            The core of the proof is that, because the edge is non-output, we know its destination
            part must correspond to an edge of only @{term y'}.\<close>
      proof -
        obtain a b and p :: "('s, 'a) port"
          where "edge_from e = edge_from a" and "a \<in> set (pg_edges x)"
            and "edge_to e = edge_to b" and "b \<in> set (pg_edges y)"
            and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
            and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
            and "port.side p = Out"
          using e(1) seqInterfaceEdges_setD by blast
        note abp = this

        have "e = renameEdge ?g (renameEdge ?f e)"
        proof -
          have "renamePlace ?g (renamePlace ?f (edge_from e)) = edge_from e"
            using abp(1,2) inv_on_places_x x.edge_from_pg by presburger
          moreover have "renamePlace ?g (renamePlace ?f (edge_to e)) = edge_to e"
            using abp(3,4) inv_on_places_y y.edge_to_pg by presburger
          ultimately show ?thesis
            by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3))
        qed
        moreover have "renameEdge ?f e \<in> set (seqInterfaceEdges x' (seqPortGraphs y' z'))"
        proof (rule seqInterfaceEdges_setI)
          show "port_graph_flow x'"
            using assms(7) .
          show "port_graph_flow (seqPortGraphs y' z')"
            using assms(8,9,11) by (rule port_graph_flow_seqPortGraphs)
          show "edge_from (renameEdge ?f e) = edge_from (renameEdge ?f a)"
            using abp(1) by simp
          show "renameEdge ?f a \<in> set (pg_edges x')"
            using abp(2) renameEdge_f_x xx'(3) by blast
          show "edge_to (renameEdge ?f e) = edge_to (renameEdge ?f b)"
            using abp(3) by simp
          have "renameEdge ?f b \<in> set (pg_edges y')"
            using abp(4) renameEdge_f_y yy'(3) by blast
          moreover have "\<not> toOpenOut b"
            using e(2) abp(3) by (simp add: toOpenOut_def)
          ultimately show "renameEdge ?f b \<in> set (pg_edges (seqPortGraphs y' z'))"
            using seqPortGraphs_flow_edges[OF assms(8,9)] by simp
          show "edge_to (renameEdge ?f a) = OpenPort (portSetSide Out p)"
            using abp(5) by simp
          show "edge_from (renameEdge ?f b) = OpenPort (portSetSide In p)"
            using abp(7) by simp
        qed
        ultimately show ?thesis
          by (smt (verit) image_eqI filter_set member_filter)
      qed
      moreover have
        " renameEdge ?g e \<in> set (seqInterfaceEdges (seqPortGraphs x y) z)
        \<or> renameEdge ?g e \<in> set (filter (\<lambda>x. \<not> toOpenOut x) (seqInterfaceEdges x y))"
        if e: "e \<in> set (seqInterfaceEdges x' (seqPortGraphs y' z'))"
        for e :: "('s, 'a, 'p) edge"
        \<comment> \<open>Edges crossing the interface of @{term x'} and @{term "seqPortGraphs y' z'"} correspond to
            either an edge in the interface of @{term "seqPortGraphs x y"} with @{term z} (i.e.\ 
            its end is the result of crossing the interface of @{term y'} and @{term z'}) or a
            non-output edge edge from just the interface of @{term x} and @{term y} (i.e.\ its end
            is an edge of only @{term y'}).
            The core of the proof is considering possible cases where the end of this edge could
            come from, eliminating contradicting cases and proving the renaming connection.\<close>
      proof -
        obtain a b and p :: "('s, 'a) port"
          where "edge_from e = edge_from a" and "a \<in> set (pg_edges x')"
            and "edge_to e = edge_to b" and "b \<in> set (pg_edges (seqPortGraphs y' z'))"
            and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
            and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
            and "port.side p = Out"
          using e(1) seqInterfaceEdges_setD by blast
        note abp = this
  
        show ?thesis
          using assms(8,9) abp(4)
        proof (cases rule: seqPortGraphs_edge_cases)
          case Stitch
          then obtain ba bb and pb :: "('s, 'a) port"
            where "edge_from b = edge_from ba" and "ba \<in> set (pg_edges y')"
              and "edge_to b = edge_to bb" and "bb \<in> set (pg_edges z')"
              and "edge_to ba = OpenPort (portSetSide Out pb)" and "edge_in_flow ba"
              and "edge_from bb = OpenPort (portSetSide In pb)" and "edge_in_flow bb"
              and "port.side pb = Out"
            using seqInterfaceEdges_setD by blast
          note bb = this
  
          have "renameEdge ?g e \<in> set (seqInterfaceEdges (seqPortGraphs x y) z)"
          proof (rule seqInterfaceEdges_setI)
            show "port_graph_flow (seqPortGraphs x y)"
              using assms(1,2,4) by (rule port_graph_flow_seqPortGraphs)
            show "port_graph_flow z"
              using assms(3) .
            show "edge_from (renameEdge ?g e) = edge_from (renameEdge ?g (Edge (edge_from a) (edge_to ba)))"
              using abp(1) by simp
            have "renameEdge ?g (Edge (edge_from a) (edge_to ba)) \<in> set (seqInterfaceEdges x y)"
            proof (rule seqInterfaceEdges_setI)
              show "port_graph_flow x"
                using assms(1) .
              show "port_graph_flow y"
                using assms(2) .
              show "edge_from (renameEdge ?g (Edge (edge_from a) (edge_to ba))) = edge_from (renameEdge ?g a)"
                using bb(1) by simp
              show "renameEdge ?g a \<in> set (pg_edges x)"
                using abp(2) renameEdge_g_x xx'(4) by blast
              show "edge_to (renameEdge ?g (Edge (edge_from a) (edge_to ba))) = edge_to (renameEdge ?g ba)"
                using bb(3) by simp
              show "renameEdge ?g ba \<in> set (pg_edges y)"
                using bb(2) renameEdge_g_y yy'(4) by blast
              show "edge_to (renameEdge ?g a) = OpenPort (portSetSide Out p)"
                using abp(5) by simp
              show "edge_from (renameEdge ?g ba) = OpenPort (portSetSide In p)"
                using bb(1) abp(7) by (metis (no_types, lifting) renameEdge_simps(2) renamePlace.simps(2))
            qed
            then show "renameEdge ?g (Edge (edge_from a) (edge_to ba)) \<in> set (pg_edges (seqPortGraphs x y))"
              by simp
            show "edge_to (renameEdge ?g e) = edge_to (renameEdge ?g bb)"
              using abp(3) bb(3) by simp
            show "renameEdge ?g bb \<in> set (pg_edges z)"
              using bb(4) renameEdge_g_z zz'(4) by blast
            show "edge_to (renameEdge ?g (Edge (edge_from a) (edge_to ba))) = OpenPort (portSetSide Out pb)"
              using bb(5) by simp
            show "edge_from (renameEdge ?g bb) = OpenPort (portSetSide In pb)"
              using bb(7) by simp
          qed
          then show ?thesis by blast
        next
          case L
  
          have "renameEdge ?g e \<in> set (seqInterfaceEdges x y)"
          proof (rule seqInterfaceEdges_setI)
            show "port_graph_flow x"
              using assms(1) .
            show "port_graph_flow y"
              using assms(2) .
            show "edge_from (renameEdge ?g e) = edge_from (renameEdge ?g a)"
              using abp(1) by simp
            show "renameEdge ?g a \<in> set (pg_edges x)"
              using abp(2) renameEdge_g_x xx'(4) by blast
            show "edge_to (renameEdge ?g e) = edge_to (renameEdge ?g b)"
              using abp(3) by simp
            show "renameEdge ?g b \<in> set (pg_edges y)"
              using L(1) renameEdge_g_y yy'(4) by blast
            show "edge_to (renameEdge ?g a) = OpenPort (portSetSide Out p)"
              using abp(5) by simp
            show "edge_from (renameEdge ?g b) = OpenPort (portSetSide In p)"
              using abp(7) by simp
          qed
          moreover have "\<not> toOpenOut (renameEdge ?g e)"
            using L(2) abp(3) by (simp add: toOpenOut_def)
          ultimately have "renameEdge ?g e \<in> set (filter (\<lambda>x. \<not> toOpenOut x) (seqInterfaceEdges x y))"
            by (smt (verit) image_eqI filter_set member_filter)
          then show ?thesis by blast
        next
          case (R b')
          then have "\<not> fromOpenIn b"
            by simp
          then show ?thesis
            using abp(7) by (simp add: fromOpenIn_def)
        qed
      qed
      moreover have
        "renameEdge ?g (shiftOpenInEdge ?shiftX' ?shiftX' e) \<in> set (seqInterfaceEdges (seqPortGraphs x y) z)"
        if e: "e \<in> set (seqInterfaceEdges y' z')" "\<not> fromOpenIn e"
        for e :: "('s, 'a, 'p) edge"
        \<comment> \<open>Non-input edges crossing the interface of @{term y'} and @{term z'} must correspond to
            a shifted edge crossing the interface of @{term "seqPortGraphs x y"} and @{term z}.
            The core of the proof is that, because the edge is non-input, we know its start must
            come only from @{term y'} and thus correspond to an edge of @{term y}.\<close>
      proof -
        obtain a b and p :: "('s, 'a) port"
          where "edge_from e = edge_from a" and "a \<in> set (pg_edges y')"
            and "edge_to e = edge_to b" and "b \<in> set (pg_edges z')"
            and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
            and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
            and "port.side p = Out"
          using e(1) seqInterfaceEdges_setD by blast
        note abp = this

        let ?witness = "renameEdge ?g (shiftOpenInEdge ?shiftX' ?shiftX' e)"
        have "?witness \<in> set (seqInterfaceEdges (seqPortGraphs x y) z)"
        proof (rule seqInterfaceEdges_setI)
          show "port_graph_flow (seqPortGraphs x y)"
            using assms(1,2,4) by (rule port_graph_flow_seqPortGraphs)
          show "port_graph_flow z"
            using assms(3) .

          have ga_in_y: "renameEdge ?g a \<in> set (pg_edges y)"
            using abp(2) renameEdge_g_y yy'(4) by blast

          have shift_a: "shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g a) = renameEdge ?g a"
          proof -
            have "place_side (edge_from (renameEdge ?g a)) = In \<or> place_side (edge_from (renameEdge ?g a)) = Out"
              using abp(6) ga_in_y y.edge_from_cases renameEdge_in_flow by blast
            then have "edge_from (shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g a)) = edge_from (renameEdge ?g a)"
              by fastforce
            moreover have "place_side (edge_to (renameEdge ?g a)) = Out"
              by (simp add: abp(5))
            then have "edge_to (shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g a)) = edge_to (renameEdge ?g a)"
              by fastforce
            ultimately show ?thesis
              using edge.expand by blast
          qed

          have "edge_from ?witness = edge_from (shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g a))"
            using abp(1) by simp
          then show "edge_from ?witness = edge_from (renameEdge ?g a)"
            using shift_a by metis

          have "\<not> fromOpenIn a"
            using e(2) abp(1) by (simp add: fromOpenIn_def)
          then have "shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g a) \<in> shiftOpenInEdge ?shiftX' ?shiftX' ` {x \<in> set (pg_edges y). \<not> fromOpenIn x}"
            using ga_in_y by simp
          then have "shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g a) \<in> set (pg_edges (seqPortGraphs x y))"
            by (unfold seqPortGraphs_flow_edges[OF assms(1,2)] set_append set_map len_fil_x set_filter)
               (intro UnI2)
          then show "renameEdge ?g a \<in> set (pg_edges (seqPortGraphs x y))"
            using shift_a by metis

          have "edge_to ?witness = edge_to (shiftOpenInEdge ?shiftX' ?shiftX' (renameEdge ?g b))"
            using abp(3) by simp
          moreover show "renameEdge ?g b \<in> set (pg_edges z)"
            using abp(4) renameEdge_g_z zz'(4) by blast
          then have "place_side (edge_to (renameEdge ?g b)) = In \<or> place_side (edge_to (renameEdge ?g b)) = Out"
            using abp(8) z.edge_to_cases renameEdge_in_flow by blast
          ultimately show "edge_to ?witness = edge_to (renameEdge ?g b)"
            by fastforce

          show "edge_to (renameEdge ?g a) = OpenPort (portSetSide Out p)"
            using abp(5) by simp
          show "edge_from (renameEdge ?g b) = OpenPort (portSetSide In p)"
            using abp(7) by simp
        qed
        then show ?thesis by blast
      qed
      ultimately show ?thesis
        \<comment> \<open>Above four cases cover all combinations of the equality.\<close>
        (* TODO by auto fails here, despite the following procedural proof *)
        apply (intro set_eqI iffI)
         apply (unfold Un_iff set_filter)
         apply (elim disjE imageE CollectE conjE)
        apply blast
        apply blast
         apply (elim disjE imageE CollectE conjE)
        apply blast
        apply blast
        done
    qed
    moreover have
      " set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x))
      = renameEdge ?g ` set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x'))"
      \<comment> \<open>Non-output edges of @{term x} are unchanged\<close>
      using renameEdge_g_x xx'(4) by (fastforce simp del: not_place_open)
    moreover have
      " shiftOpenInEdge ?shiftX ?shiftX ` set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y))
      = renameEdge ?g ` shiftOpenInEdge ?shiftX' ?shiftX' ` set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y'))"
      \<comment> \<open>Non-flow edges of @{term y} are shifted by @{term x}'s\<close>
    proof -
      have
        " set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y))
        = renameEdge ?g ` set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y'))"
        using renameEdge_g_y yy'(4) by (fastforce simp del: not_place_open)
      then have
        " shiftOpenInEdge ?shiftX ?shiftX ` set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y))
        = renameEdge ?g ` shiftOpenInEdge ?shiftX ?shiftX ` set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y'))"
        using renameEdge_shiftOpenInEdge by (metis (no_types, lifting) image_comm)
      then show ?thesis
        by (fold len_fil_x)
    qed
    moreover have
      " shiftOpenInEdge ?shiftXY ?shiftXY ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z))
      = renameEdge ?g ` shiftOpenInEdge ?shiftX' ?shiftX' ` shiftOpenInEdge ?shiftY' ?shiftY' ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z'))"
      \<comment> \<open>Non-input edges of @{term z} are shifted by both @{term x}'s and @{term y}'s.\<close>
    proof -
      have
        " set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z))
        = renameEdge ?g ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z'))"
        using renameEdge_g_z zz'(4) by (fastforce simp del: not_place_open)
      then have
        " shiftOpenInEdge ?shiftXY ?shiftXY ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z))
        = renameEdge ?g ` shiftOpenInEdge ?shiftXY ?shiftXY ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z'))"
        using renameEdge_shiftOpenInEdge by (metis (no_types, lifting) image_comm)
      moreover have "?shiftXY s = ?shiftX' s + ?shiftY' s" for s :: 's
        by (clarsimp simp add: len_fil_x len_fil_y) (smt (verit, del_insts) filter_cong)
      then have "shiftOpenInEdge ?shiftXY ?shiftXY ` A = shiftOpenInEdge ?shiftX' ?shiftX' ` shiftOpenInEdge ?shiftY' ?shiftY' ` A"
        for A :: "('s, 'a, 'p) edge set"
        by (simp add: image_comp)
      ultimately show ?thesis
        by metis
    qed
    ultimately have combined:
      " set (seqInterfaceEdges (seqPortGraphs x y) z) \<union>
        set (filter (\<lambda>x. \<not> toOpenOut x) (seqInterfaceEdges x y)) \<union>
        set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x)) \<union>
        shiftOpenInEdge ?shiftX ?shiftX ` set (filter (\<lambda>x. \<not> fromOpenIn x \<and> \<not> toOpenOut x) (pg_edges y)) \<union>
        shiftOpenInEdge ?shiftXY ?shiftXY ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z))
      = renameEdge ?g ` set (seqInterfaceEdges x' (seqPortGraphs y' z')) \<union>
        renameEdge ?g ` set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x')) \<union>
        renameEdge ?g ` shiftOpenInEdge ?shiftX' ?shiftX' ` set (filter (\<lambda>x. \<not> fromOpenIn x) (seqInterfaceEdges y' z')) \<union>
        renameEdge ?g ` shiftOpenInEdge ?shiftX' ?shiftX' ` set (filter (\<lambda>x. \<not> toOpenOut x \<and> \<not> fromOpenIn x) (pg_edges y')) \<union>
        renameEdge ?g `
        shiftOpenInEdge ?shiftX' ?shiftX' ` shiftOpenInEdge ?shiftY' ?shiftY' ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges z'))"
      \<comment> \<open>Gather these together into one statement about the edge sets.\<close>
      by (smt (verit) filter_cong sup_assoc sup_commute)

    have "port_graph_flow (seqPortGraphs y' z')"
      using assms(8,9,11) by (rule port_graph_flow_seqPortGraphs)
    moreover have "port_graph_flow (seqPortGraphs x y)"
      using assms(1,2,4) by (rule port_graph_flow_seqPortGraphs)
    ultimately show ?thesis
      \<comment> \<open>To complete, simplify the two levels of combinations on both sides,\<close>
      using x.port_graph_flow_axioms y.port_graph_flow_axioms z.port_graph_flow_axioms
      using x'.port_graph_flow_axioms y'.port_graph_flow_axioms z'.port_graph_flow_axioms
      apply (simp only: seqPortGraphs_flow_edges)
      \<comment> \<open>Simplify the result,\<close>
      unfolding set_append image_Un filter_map filter_append shiftOpenInEdge_toOpenOut filter_filter
        conj_absorb comp_def Un_assoc[symmetric] set_map[where f = "shiftOpenInEdge _ _"]
        shiftOpenInEdge_fromOpenIn
      \<comment> \<open>Apply the combined statement to the simplified goal.\<close>
      by (rule combined)
  qed
  moreover have "?g (?f l) = l"
    if l_in: "l \<in> node_name ` set (pg_nodes (seqPortGraphs (seqPortGraphs x y) z))" for l
  proof -
    obtain n
      where "n \<in> set (pg_nodes (seqPortGraphs (seqPortGraphs x y) z))" and l: "l = node_name n"
      using l_in by blast
    then consider
        (X) "n \<in> set (pg_nodes x)" and "n \<notin> set (pg_nodes y)" and "n \<notin> set (pg_nodes z)"
      | (Y) "n \<notin> set (pg_nodes x)" and "n \<in> set (pg_nodes y)" and "n \<notin> set (pg_nodes z)"
      | (Z) "n \<notin> set (pg_nodes x)" and "n \<notin> set (pg_nodes y)" and "n \<in> set (pg_nodes z)"
      using assms by (blast elim: in_nodes_seqPortGraphsE)
    then show ?thesis
    proof cases
      case X
      then show ?thesis
        using xx'(1,6) renameNode_f_x renameNode_g_x l
        by (smt (z3) image_iff renameNode_simps(2))
    next
      case Y
      then have "node_name n \<notin> node_name ` set (pg_nodes x)"
        using assms(4) by fastforce
      then show ?thesis
        using Y yy'(1,6) renameNode_f_y renameNode_g_y l
        by (smt (z3) image_iff renameNode_simps(2))
    next
      case Z
      then have "node_name n \<notin> node_name ` set (pg_nodes x)"
        using assms(6) by fastforce
      moreover have "node_name n \<notin> node_name ` set (pg_nodes y)"
        using Z assms(5) by fastforce
      ultimately show ?thesis
        using Z zz'(1,6) renameNode_f_z renameNode_g_z l
        by (smt (z3) image_iff renameNode_simps(2))
    qed
  qed
  moreover have "?f (?g l) = l"
    if l_in: "l \<in> node_name ` set (pg_nodes (seqPortGraphs x' (seqPortGraphs y' z')))" for l
  proof -
    obtain n
      where "n \<in> set (pg_nodes (seqPortGraphs x' (seqPortGraphs y' z')))" and l: "l = node_name n"
      using l_in by blast
    then consider
      (X) "n \<in> set (pg_nodes x')" and "n \<notin> set (pg_nodes y')" and "n \<notin> set (pg_nodes z')"
      | (Y) "n \<notin> set (pg_nodes x')" and "n \<in> set (pg_nodes y')" and "n \<notin> set (pg_nodes z')"
      | (Z) "n \<notin> set (pg_nodes x')" and "n \<notin> set (pg_nodes y')" and "n \<in> set (pg_nodes z')"
      using assms by (blast elim: in_nodes_seqPortGraphsE)
    then show ?thesis
    proof cases
      case X
      then show ?thesis
        using xx'(2,7) renameNode_f_x renameNode_g_x l
        by (smt (z3) image_iff renameNode_simps(2))
    next
      case Y
      then have "node_name n \<notin> node_name ` set (pg_nodes x')"
        using assms(10) by fastforce
      then show ?thesis
        using Y yy'(2,7) renameNode_f_y renameNode_g_y l
        by (smt (z3) image_iff renameNode_simps(2))
    next
      case Z
      then have "node_name n \<notin> node_name ` set (pg_nodes x')"
        using assms(12) by fastforce
      moreover have "node_name n \<notin> node_name ` set (pg_nodes y')"
        using Z assms(11) by fastforce
      ultimately show ?thesis
        using Z zz'(2,7) renameNode_f_z renameNode_g_z l
        by (smt (z3) image_iff renameNode_simps(2))
    qed
  qed
  ultimately have "pgEquiv_witness ?f ?g (seqPortGraphs (seqPortGraphs x y) z) (seqPortGraphs x' (seqPortGraphs y' z'))"
    by (rule pgEquiv_witnessI)
  then show "\<exists>f g. pgEquiv_witness f g (seqPortGraphs (seqPortGraphs x y) z) (seqPortGraphs x' (seqPortGraphs y' z'))"
    by blast
qed

lemma seqPortGraphs_assoc:
  fixes x y z :: "('s :: side_in_out, 'a, 'p, 'l) port_graph"
  assumes "port_graph_flow x"
      and "port_graph_flow y"
      and "port_graph_flow z"
      and "pg_disjoint x y"
      and "pg_disjoint y z"
      and "pg_disjoint x z"
    shows "seqPortGraphs (seqPortGraphs x y) z \<approx> seqPortGraphs x (seqPortGraphs y z)"
  using assms assms pgEquiv_refl pgEquiv_refl pgEquiv_refl
  by (rule seqPortGraphs_assoc_pgEquiv)

subsection\<open>Qualification\<close>

text\<open>
  Qualifying a sequential composition of port graphs is the same as sequential composition of
  qualified port graphs.
\<close>
lemma qualifyPortGraph_seqPortGraphs [simp]:
  "qualifyPortGraph a (seqPortGraphs x y) = seqPortGraphs (qualifyPortGraph a x) (qualifyPortGraph a y)"
proof -
  have
    " map (qualifyEdge a) (disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = Out) (pg_ports x))) (pg_edges x)) =
      disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = Out) (pg_ports x))) (map (qualifyEdge a) (pg_edges x))"
    by (simp_all add: qualifyEdge_disconnectFromPlaces comp_def)
  moreover have
    " map (qualifyEdge a) (disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = In) (pg_ports y))) (pg_edges y)) =
      disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = In) (pg_ports y))) (map (qualifyEdge a) (pg_edges y))"
    by (simp_all add: qualifyEdge_disconnectFromPlaces comp_def)
  ultimately show ?thesis
    by (simp add: qualifyPortGraph_def map_qualifyEdge_shiftOpenInEdge seqInterfaceEdges_qualify
             del: seqInterfaceEdges.simps map_map)
       (metis port_graph.sel(3))
qed

subsection\<open>Respecting Equivalence\<close>

text\<open>Sequencing respects port graph equivalence\<close>
lemma seqPortGraphs_resp:
  fixes x y x' y' :: "('s :: side_in_out, 'a, 'p, 'l) port_graph"
  assumes "port_graph_flow x"
      and "port_graph_flow y"
      and "pg_disjoint x y"
      and "port_graph_flow x'"
      and "port_graph_flow y'"
      and "pg_disjoint x' y'"
      and "x \<approx> x'"
      and "y \<approx> y'"
    shows "seqPortGraphs x y \<approx> seqPortGraphs x' y'"
proof (rule pgEquivI_ex)
  interpret x: port_graph_flow x using assms by simp
  interpret y: port_graph_flow y using assms by simp
  interpret x': port_graph_flow x' using assms by simp
  interpret y': port_graph_flow y' using assms by simp

  show "port_graph (seqPortGraphs x y)"
    by (metis assms(1-3) port_graph_flow.axioms(1) port_graph_flow_seqPortGraphs)
  show "port_graph (seqPortGraphs x' y')"
    by (metis assms(4-6) port_graph_flow.axioms(1) port_graph_flow_seqPortGraphs)

  note pg_x = x.port_graph_axioms
  moreover note pg_x' = x'.port_graph_axioms
  ultimately obtain f_x g_x
    where "renameNode f_x ` (set (pg_nodes x)) = set (pg_nodes x')"
      and "set (pg_nodes x) = renameNode g_x ` (set (pg_nodes x'))"
      and "renameEdge f_x ` (set (pg_edges x)) = set (pg_edges x')"
      and "set (pg_edges x) = renameEdge g_x ` (set (pg_edges x'))"
      and p_xx': "set (pg_ports x) = set (pg_ports x')"
      and "\<And>l. l \<in> node_name ` set (pg_nodes x) \<Longrightarrow> g_x (f_x l) = l"
      and "\<And>l. l \<in> node_name ` set (pg_nodes x') \<Longrightarrow> f_x (g_x l) = l"
    using assms(7) by (elim pgEquivE ; blast)
  note xx' = this

  note pg_y = y.port_graph_axioms
  moreover note pg_y' = y'.port_graph_axioms
  ultimately obtain f_y g_y
    where "renameNode f_y ` (set (pg_nodes y)) = set (pg_nodes y')"
      and "set (pg_nodes y) = renameNode g_y ` (set (pg_nodes y'))"
      and "renameEdge f_y ` (set (pg_edges y)) = set (pg_edges y')"
      and "set (pg_edges y) = renameEdge g_y ` (set (pg_edges y'))"
      and p_yy': "set (pg_ports y) = set (pg_ports y')"
      and "\<And>l. l \<in> node_name ` set (pg_nodes y) \<Longrightarrow> g_y (f_y l) = l"
      and "\<And>l. l \<in> node_name ` set (pg_nodes y') \<Longrightarrow> f_y (g_y l) = l"
    using assms(8) by (elim pgEquivE ; blast)
  note yy' = this

  have len_fil_x: "length (filter P (pg_ports x)) = length (filter P (pg_ports x'))" for P
    using xx'(5) x.ports_distinct x'.ports_distinct
    by (metis distinct_length_filter)
  have len_fil_y: "length (filter P (pg_ports y)) = length (filter P (pg_ports y'))" for P
    using yy'(5) y.ports_distinct y'.ports_distinct
    by (metis distinct_length_filter)

  show "set (pg_ports (seqPortGraphs x y)) = set (pg_ports (seqPortGraphs x' y'))"
    using p_xx' p_yy' len_fil_x by simp

  let ?f = "\<lambda>p.
    if p \<in> set (map node_name (pg_nodes x))
      then f_x p
      else if p \<in> set (map node_name (pg_nodes y))
        then f_y p
        else undefined"

  (* TODO I wish there was a command to assign a list of theorems in sequence to a list of names *)
  note thm_buffer = pgEquiv_witness_combine_2[OF pg_x pg_y assms(3), where f_x = f_x and f_y = f_y]
  note renameNode_f_x = thm_buffer(1)
  note renameNode_f_y = thm_buffer(2)
  note renameEdge_f_x = thm_buffer(5)
  note renameEdge_f_y = thm_buffer(6)

  let ?g = "\<lambda>p.
    if p \<in> set (map node_name (pg_nodes x'))
      then g_x p
      else if p \<in> set (map node_name (pg_nodes y'))
        then g_y p
        else undefined"

  (* TODO I wish there was a command to assign a list of theorems in sequence to a list of names *)
  note thm_buffer = pgEquiv_witness_combine_2[OF pg_x' pg_y' assms(6), where f_x = g_x and f_y = g_y]
  note renameNode_g_x = thm_buffer(1)
  note renameNode_g_y = thm_buffer(2)
  note renameEdge_g_x = thm_buffer(5)
  note renameEdge_g_y = thm_buffer(6)

  have inv_on_places_x:
    "renamePlace ?g (renamePlace ?f p) = p" if p_in: "p \<in> set (pgraphPlaces x)" for p
  proof (cases p)
    case (GroundPort qp)
    then obtain n p'
      where "n \<in> set (pg_nodes x)" and "p' \<in> set (node_ports n)"
        and p: "p = GroundPort (QPort p' (node_name n))"
      using GroundPort p_in by fastforce
    then show ?thesis
      by (simp add: xx'(6)) (metis xx'(1) imageI renameNode_simps(2))
  next case (OpenPort p') then show ?thesis by simp
  qed
  then have inv_on_edges_x:
    "e \<in> set (pg_edges x) \<Longrightarrow> renameEdge ?g (renameEdge ?f e) = e" for e
    by (rule x.inv_on_edges)

  have inv_on_places_y:
    "renamePlace ?g (renamePlace ?f p) = p" if p_in: "p \<in> set (pgraphPlaces y)" for p
  proof (cases p)
    case (GroundPort qp)
    then obtain n p'
      where n: "n \<in> set (pg_nodes y)" and "p' \<in> set (node_ports n)"
        and "p = GroundPort (QPort p' (node_name n))"
      using that p_in by fastforce
    moreover have "node_name n \<notin> node_name ` set (pg_nodes x)"
      using n assms(3) by fastforce
    ultimately show ?thesis
      using renameNode_g_y yy'(6)
      by simp (smt (z3) yy'(1) imageI renameNode_simps(2))
  next case (OpenPort p') then show ?thesis by simp
  qed
  then have inv_on_edges_y:
    "e \<in> set (pg_edges y) \<Longrightarrow> renameEdge ?g (renameEdge ?f e) = e" for e
    by (rule y.inv_on_edges)

  have inv_on_places_x':
    "renamePlace ?f (renamePlace ?g p) = p" if p_in: "p \<in> set (pgraphPlaces x')" for p
  proof (cases p)
    case (GroundPort qp)
    then obtain n p'
      where "n \<in> set (pg_nodes x')" and "p' \<in> set (node_ports n)"
        and p: "p = GroundPort (QPort p' (node_name n))"
      using GroundPort p_in by fastforce
    then show ?thesis
      by (simp add: xx'(7)) (metis xx'(2) imageI renameNode_simps(2))
  next case (OpenPort p') then show ?thesis by simp
  qed
  then have inv_on_edges_x':
    "e \<in> set (pg_edges x') \<Longrightarrow> renameEdge ?f (renameEdge ?g e) = e" for e
    by (rule x'.inv_on_edges)

  have inv_on_places_y':
    "renamePlace ?f (renamePlace ?g p) = p" if p_in: "p \<in> set (pgraphPlaces y')" for p
  proof (cases p)
    case (GroundPort qp)
    then obtain n p'
      where n: "n \<in> set (pg_nodes y')" and "p' \<in> set (node_ports n)"
        and "p = GroundPort (QPort p' (node_name n))"
      using that p_in by fastforce
    moreover have "node_name n \<notin> node_name ` set (pg_nodes x')"
      using n assms(6) by fastforce
    ultimately show ?thesis
      using renameNode_f_y yy'(7)
      by simp (smt (z3) yy'(2) imageI renameNode_simps(2))
  next case (OpenPort p') then show ?thesis by simp
  qed
  then have inv_on_edges_y':
    "e \<in> set (pg_edges y') \<Longrightarrow> renameEdge ?f (renameEdge ?g e) = e" for e
    by (rule y'.inv_on_edges)

  \<comment> \<open>Set up shorthands for the many used edge/place shift amounts.\<close>
  let ?shiftX = "(\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))"
  let ?shiftX' = "(\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x')))"

  have "renameNode ?f ` set (pg_nodes (seqPortGraphs x y)) = set (pg_nodes (seqPortGraphs x' y'))"
    \<comment> \<open>Prove connection between node sets separately for each port graph's nodes, then combine.\<close>
  proof -
    have "renameNode ?f ` set (pg_nodes x) = set (pg_nodes x')"
      using renameNode_f_x xx'(1) by simp
    moreover have "renameNode ?f ` set (pg_nodes y) = set (pg_nodes y')"
      using renameNode_f_y yy'(1) by simp
    ultimately show ?thesis
      by (simp add: image_Un)
  qed
  moreover have "set (pg_nodes (seqPortGraphs x y)) = renameNode ?g ` set (pg_nodes (seqPortGraphs x' y'))"
    \<comment> \<open>Prove connection between node sets separately for each port graph's nodes, then combine.\<close>
  proof -
    have "set (pg_nodes x) = renameNode ?g ` set (pg_nodes x')"
      using renameNode_g_x xx'(2) by simp
    moreover have "set (pg_nodes y) = renameNode ?g ` set (pg_nodes y')"
      using renameNode_g_y yy'(2) by simp
    ultimately show ?thesis
      by (simp add: image_Un)
  qed
  moreover have "renameEdge ?f ` set (pg_edges (seqPortGraphs x y)) = set (pg_edges (seqPortGraphs x' y'))"
    \<comment> \<open>Prove connection between edge sets by proving which of their parts connect and combining
        those facts together.\<close>
  proof -
    have "renameEdge ?f ` set (seqInterfaceEdges x y) = set (seqInterfaceEdges x' y')"
      \<comment> \<open>Most complex are edges crossing the interfaces, which split into two cases (one for each
          direction of the inclusion).\<close>
    proof safe
      fix e
      assume e: "e \<in> set (seqInterfaceEdges x y)"

      obtain a b and p :: "('s, 'a) port"
        where "edge_from e = edge_from a" and "a \<in> set (pg_edges x)"
          and "edge_to e = edge_to b" and "b \<in> set (pg_edges y)"
          and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
          and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
          and "port.side p = Out"
        using e seqInterfaceEdges_setD by blast
      note abp = this

      show "renameEdge ?f e \<in> set (seqInterfaceEdges x' y')"
      proof (rule seqInterfaceEdges_setI)
        show "port_graph_flow x'"
          using assms(4) .
        show "port_graph_flow y'"
          using assms(5) .
        show "edge_from (renameEdge ?f e) = edge_from (renameEdge ?f a)"
          using abp(1) by simp
        show "renameEdge ?f a \<in> set (pg_edges x')"
          using abp(2) renameEdge_f_x xx'(3) by blast
        show "edge_to (renameEdge ?f e) = edge_to (renameEdge ?f b)"
          using abp(3) by simp
        show "renameEdge ?f b \<in> set (pg_edges y')"
          using abp(4) renameEdge_f_y yy'(3) by blast
        show "edge_to (renameEdge ?f a) = OpenPort (portSetSide Out p)"
          using abp(5) by simp
        show "edge_from (renameEdge ?f b) = OpenPort (portSetSide In p)"
          using abp(7) by simp
      qed
    next
      fix e
      assume e: "e \<in> set (seqInterfaceEdges x' y')"

      obtain a b and p :: "('s, 'a) port"
        where "edge_from e = edge_from a" and "a \<in> set (pg_edges x')"
          and "edge_to e = edge_to b" and "b \<in> set (pg_edges y')"
          and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
          and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
          and "port.side p = Out"
        using e seqInterfaceEdges_setD by blast
      note abp = this

      have "e = renameEdge ?f (renameEdge ?g e)"
      proof -
        have "renamePlace ?f (renamePlace ?g (edge_from e)) = edge_from e"
          using abp(1,2) inv_on_places_x' x'.edge_from_pg by presburger
        moreover have "renamePlace ?f (renamePlace ?g (edge_to e)) = edge_to e"
          using abp(3,4) inv_on_places_y' y'.edge_to_pg by presburger
        ultimately show ?thesis
          by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3))
      qed
      moreover have "renameEdge ?g e \<in> set (seqInterfaceEdges x y)"
      proof (rule seqInterfaceEdges_setI)
        show "port_graph_flow x"
          using assms(1) .
        show "port_graph_flow y"
          using assms(2) .
        show "edge_from (renameEdge ?g e) = edge_from (renameEdge ?g a)"
          using abp(1) by simp
        show "renameEdge ?g a \<in> set (pg_edges x)"
          using abp(2) renameEdge_g_x xx'(4) by blast
        show "edge_to (renameEdge ?g e) = edge_to (renameEdge ?g b)"
          using abp(3) by simp
        show "renameEdge ?g b \<in> set (pg_edges y)"
          using abp(4) renameEdge_g_y yy'(4) by blast
        show "edge_to (renameEdge ?g a) = OpenPort (portSetSide Out p)"
          using abp(5) by simp
        show "edge_from (renameEdge ?g b) = OpenPort (portSetSide In p)"
          using abp(7) by simp
      qed
      ultimately show "e \<in> renameEdge ?f ` set (seqInterfaceEdges x y)"
        by blast
    qed
    moreover have
      " renameEdge ?f ` set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x))
      = set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x'))"
      \<comment> \<open>Non-output edges of @{term x} must correspond to an edge of @{term x'}.\<close>
      using renameEdge_f_x xx'(3) by (fastforce simp del: not_place_open)
    moreover have
      " renameEdge ?f ` set (map (shiftOpenInEdge ?shiftX ?shiftX) (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y)))
      = set (map (shiftOpenInEdge ?shiftX' ?shiftX') (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y')))"
      \<comment> \<open>Non-input edges of @{term y} must correspond to an edge of @{term y'}, accounting for
          equivalent shifting.\<close>
    proof -
      have
        " renameEdge ?f ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y))
        = set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y'))"
        using renameEdge_f_y yy'(3) by (fastforce simp del: not_place_open)
      then have
        " renameEdge ?f ` shiftOpenInEdge ?shiftX ?shiftX ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y))
        = shiftOpenInEdge ?shiftX ?shiftX ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y'))"
        using renameEdge_shiftOpenInEdge by (metis (no_types, lifting) image_comm)
      then show ?thesis
        by (fold len_fil_x set_map)
    qed
    ultimately show ?thesis
      using x.port_graph_flow_axioms y.port_graph_flow_axioms
      using x'.port_graph_flow_axioms y'.port_graph_flow_axioms
      by (simp only: seqPortGraphs_flow_edges) (simp add: image_Un)
  qed
  moreover have "set (pg_edges (seqPortGraphs x y)) = renameEdge ?g ` set (pg_edges (seqPortGraphs x' y'))"
    \<comment> \<open>Prove connection between edge sets by proving which of their parts connect and combining
        those facts together.\<close>
  proof -
    have "set (seqInterfaceEdges x y) = renameEdge ?g ` set (seqInterfaceEdges x' y')"
      \<comment> \<open>Most complex are edges crossing the interfaces, which split into two cases (one for each
          direction of the inclusion).\<close>
    proof safe
      fix e
      assume e: "e \<in> set (seqInterfaceEdges x' y')"

      obtain a b and p :: "('s, 'a) port"
        where "edge_from e = edge_from a" and "a \<in> set (pg_edges x')"
          and "edge_to e = edge_to b" and "b \<in> set (pg_edges y')"
          and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
          and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
          and "port.side p = Out"
        using e seqInterfaceEdges_setD by blast
      note abp = this

      show "renameEdge ?g e \<in> set (seqInterfaceEdges x y)"
      proof (rule seqInterfaceEdges_setI)
        show "port_graph_flow x"
          using assms(1) .
        show "port_graph_flow y"
          using assms(2) .
        show "edge_from (renameEdge ?g e) = edge_from (renameEdge ?g a)"
          using abp(1) by simp
        show "renameEdge ?g a \<in> set (pg_edges x)"
          using abp(2) renameEdge_g_x xx'(4) by blast
        show "edge_to (renameEdge ?g e) = edge_to (renameEdge ?g b)"
          using abp(3) by simp
        show "renameEdge ?g b \<in> set (pg_edges y)"
          using abp(4) renameEdge_g_y yy'(4) by blast
        show "edge_to (renameEdge ?g a) = OpenPort (portSetSide Out p)"
          using abp(5) by simp
        show "edge_from (renameEdge ?g b) = OpenPort (portSetSide In p)"
          using abp(7) by simp
      qed
    next
      fix e
      assume e: "e \<in> set (seqInterfaceEdges x y)"

      obtain a b and p :: "('s, 'a) port"
        where "edge_from e = edge_from a" and "a \<in> set (pg_edges x)"
          and "edge_to e = edge_to b" and "b \<in> set (pg_edges y)"
          and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
          and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
          and "port.side p = Out"
        using e seqInterfaceEdges_setD by blast
      note abp = this

      have "e = renameEdge ?g (renameEdge ?f e)"
      proof -
        have "renamePlace ?g (renamePlace ?f (edge_from e)) = edge_from e"
          using abp(1,2) inv_on_places_x x.edge_from_pg by presburger
        moreover have "renamePlace ?g (renamePlace ?f (edge_to e)) = edge_to e"
          using abp(3,4) inv_on_places_y y.edge_to_pg by presburger
        ultimately show ?thesis
          by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3))
      qed
      moreover have "renameEdge ?f e \<in> set (seqInterfaceEdges x' y')"
      proof (rule seqInterfaceEdges_setI)
        show "port_graph_flow x'"
          using assms(4) .
        show "port_graph_flow y'"
          using assms(5) .
        show "edge_from (renameEdge ?f e) = edge_from (renameEdge ?f a)"
          using abp(1) by simp
        show "renameEdge ?f a \<in> set (pg_edges x')"
          using abp(2) renameEdge_f_x xx'(3) by blast
        show "edge_to (renameEdge ?f e) = edge_to (renameEdge ?f b)"
          using abp(3) by simp
        show "renameEdge ?f b \<in> set (pg_edges y')"
          using abp(4) renameEdge_f_y yy'(3) by blast
        show "edge_to (renameEdge ?f a) = OpenPort (portSetSide Out p)"
          using abp(5) by simp
        show "edge_from (renameEdge ?f b) = OpenPort (portSetSide In p)"
          using abp(7) by simp
      qed
      ultimately show "e \<in> renameEdge ?g ` set (seqInterfaceEdges x' y')"
        by blast
    qed
    moreover have
      " set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x))
      = renameEdge ?g ` set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x'))"
      \<comment> \<open>Non-output edges of @{term x} must correspond to an edge of @{term x'}.\<close>
    proof safe
      fix e
      assume e: "e \<in> set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x))"

      have "e = renameEdge ?g (renameEdge ?f e)"
        using e inv_on_edges_x by fastforce
      moreover have "renameEdge ?f e \<in> set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x'))"
        using e renameEdge_f_x xx'(3) by auto
      ultimately show "e \<in> renameEdge ?g ` set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x'))"
        by blast
    next
      fix e
      assume "e \<in> set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x'))"

      then show "renameEdge ?g e \<in> set (filter (\<lambda>x. \<not> toOpenOut x) (pg_edges x))"
        using renameEdge_g_x xx'(4) by auto
    qed
    moreover have
      " set (map (shiftOpenInEdge ?shiftX ?shiftX) (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y)))
      = renameEdge ?g ` set (map (shiftOpenInEdge ?shiftX' ?shiftX') (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y')))"
      \<comment> \<open>Non-input edges of @{term y} must correspond to an edge of @{term y'}, accounting for
          equivalent shifting.\<close>
    proof -
      have
        " set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y))
        = renameEdge ?g ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y'))"
      proof safe
        fix e
        assume e: "e \<in> set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y))"
  
        have "e = renameEdge ?g (renameEdge ?f e)"
          using e inv_on_edges_y by fastforce
        moreover have "renameEdge ?f e \<in> set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y'))"
          using e renameEdge_f_y yy'(3) by auto
        ultimately show "e \<in> renameEdge ?g ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y'))"
          by blast
      next
        fix e
        assume "e \<in> set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y'))"
  
        then show "renameEdge ?g e \<in> set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y))"
          using renameEdge_g_y yy'(4) by auto
      qed
      then have
        " shiftOpenInEdge ?shiftX ?shiftX ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y))
        = renameEdge ?g ` shiftOpenInEdge ?shiftX ?shiftX ` set (filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges y'))"
        using renameEdge_shiftOpenInEdge by (metis (no_types, lifting) image_comm)
      then show ?thesis
        by (fold len_fil_x set_map)
    qed
    ultimately show ?thesis
      using x.port_graph_flow_axioms y.port_graph_flow_axioms
      using x'.port_graph_flow_axioms y'.port_graph_flow_axioms
      by (simp only: seqPortGraphs_flow_edges) (simp add: image_Un)
  qed
  moreover have "?g (?f l) = l" if "l \<in> node_name ` set (pg_nodes (seqPortGraphs x y))" for l
    using that renameNode_f_x renameNode_f_y renameNode_g_x renameNode_g_y xx'(1,6) yy'(1,6)
    by (smt (z3) image_iff in_nodes_seqPortGraphsE renameNode_simps(2))
  moreover have "?f (?g l) = l" if "l \<in> node_name ` set (pg_nodes (seqPortGraphs x' y'))" for l
    using that renameNode_f_x renameNode_f_y renameNode_g_x renameNode_g_y xx'(2,7) yy'(2,7)
    by (smt (z3) image_iff in_nodes_seqPortGraphsE renameNode_simps(2))
  ultimately have "pgEquiv_witness ?f ?g (seqPortGraphs x y) (seqPortGraphs x' y')"
    using pgEquiv_witnessI by blast
  then show "\<exists>f g. pgEquiv_witness f g (seqPortGraphs x y) (seqPortGraphs x' y')"
    by blast
qed

end
