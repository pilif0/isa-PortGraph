theory Equivalences
  imports
    Juxtapose
    Sequence
    IdentityPortGraph
    SwapPortGraph
    ForkPortGraph
    EndPortGraph
begin

section\<open>Port Graph Equivalences (and Equations)\<close>

subsection\<open>Swap as Sequential Inverse\<close>

text\<open>
  If all edges we are grouping by open output destinations have destinations distinct open
  ports, then grouping them is a simple mapping of output port to just its edge.
\<close>
lemma edgesByOpenTo_all_to_distinct:
  assumes "\<And>e. e \<in> set es \<Longrightarrow> place_open (edge_to e)"
      and "\<And>n1 n2. \<lbrakk>n1 \<noteq> n2; n1 < length es; n2 < length es\<rbrakk> \<Longrightarrow> edge_to (es ! n1) \<noteq> edge_to (es ! n2)"
    shows "edgesByOpenTo es = Mapping (map (\<lambda>e. (place_port (edge_to e), [e])) es)"
  using assms
proof (induct es)
  case Nil
  then show ?case by (simp add: empty_Mapping)
next
  case (Cons a es)

  show ?case
    using Cons.prems
    apply (simp add: map_default_def default_def)
    apply safe
    apply (subst (asm) Cons.hyps)
    apply blast
      apply (metis Suc_inject not_less_eq nth_Cons_Suc)
     apply (clarsimp)
     apply (metis (no_types, opaque_lifting) Suc_mono Zero_not_Suc bot_nat_0.not_eq_extremum in_set_conv_nth
        nth_Cons_0 nth_Cons_Suc place.collapse(2) place_port.simps(2))
    apply (simp add: map_entry_code)
    apply (subst Cons.hyps)
    apply blast
     apply (metis Suc_inject not_less_eq nth_Cons_Suc)
    apply (simp add: update_Mapping)
    apply (subst (asm) Cons.hyps)
    apply blast
      apply (metis Suc_inject not_less_eq nth_Cons_Suc)
    apply (clarsimp)
    apply (rule Mapping_AList_update_is_Cons)
    apply clarsimp
    done
qed

text\<open>
  If all edges we are grouping by open input origins have origins distinct open ports, then
  grouping them is a simple mapping of input port to just its edge.
\<close>
lemma edgesByOpenFrom_all_from_distinct:
  assumes "\<And>e. e \<in> set es \<Longrightarrow> place_open (edge_from e)"
      and "\<And>n1 n2. \<lbrakk>n1 \<noteq> n2; n1 < length es; n2 < length es\<rbrakk> \<Longrightarrow> edge_from (es ! n1) \<noteq> edge_from (es ! n2)"
    shows "edgesByOpenFrom es = Mapping (map (\<lambda>e. (place_port (edge_from e), [e])) es)"
  using assms
proof (induct es)
  case Nil
  then show ?case by (simp add: empty_Mapping)
next
  case (Cons a es)

  show ?case
    using Cons.prems
    apply (simp add: map_default_def default_def)
    apply safe
    apply (subst (asm) Cons.hyps)
    apply blast
      apply (metis Suc_inject not_less_eq nth_Cons_Suc)
     apply (clarsimp)
     apply (metis (no_types, opaque_lifting) Suc_mono Zero_not_Suc bot_nat_0.not_eq_extremum in_set_conv_nth
        nth_Cons_0 nth_Cons_Suc place.collapse(2) place_port.simps(2))
    apply (simp add: map_entry_code)
    apply (subst Cons.hyps)
    apply blast
     apply (metis Suc_inject not_less_eq nth_Cons_Suc)
    apply (simp add: update_Mapping)
    apply (subst (asm) Cons.hyps)
    apply blast
      apply (metis Suc_inject not_less_eq nth_Cons_Suc)
    apply (clarsimp)
    apply (rule Mapping_AList_update_is_Cons)
    apply clarsimp
    done
qed

(* TODO doc and move this situational theorem *)
lemma map_of_map_key_value:
  assumes "inj_on k (set xs)"
      and "x \<in> set xs"
    shows "map_of (map (\<lambda>x. (k x, v x)) xs) (k x) = map_of (map (\<lambda>x. (x, v x)) xs) x"
  using assms apply (induct xs arbitrary: x)
   apply simp
  apply simp
  apply safe
  apply (simp add: rev_image_eqI)
  apply simp
  done

text\<open>
  Sequential composition of opposite swaps is equivalent to identity.
  Note that this is an equivalence, since the order of edges is different: they follow the interface
  on which the sequential composition happens, which orders them as @{term "bs @ as"}.
\<close>
lemma seqPortGraphs_swap_inverse:
  " seqPortGraphs (swapPortGraph as bs) (swapPortGraph bs as)
  \<approx> (idPortGraph (as @ bs) :: ('s :: side_in_out, 'a, 'p, 'l) port_graph)"
  \<comment> \<open>Prove by showing that the edge, node and port sets are the same\<close>
proof (rule pgEquiv_permute)
  \<comment> \<open>Prove the simple conditions first, followed by the edges.\<close>
  show "port_graph (seqPortGraphs (swapPortGraph as bs) (swapPortGraph bs as))"
    \<comment> \<open>Left-hand port graph is well-formed\<close>
    using port_graph_flow_seqPortGraphs port_graph_flow_swapPortGraph pg_disjoint_trivialI1
    by (metis port_graph.sel(1) port_graph_flow.axioms(1) swapPortGraph.simps)
  show
    " set (pg_nodes (seqPortGraphs (swapPortGraph as bs) (swapPortGraph bs as)))
    = set (pg_nodes (idPortGraph (as @ bs)))"
    \<comment> \<open>Node sets are empty for both, and so the same\<close>
    by simp

  show
    " set (pg_edges (seqPortGraphs (swapPortGraph as bs) (swapPortGraph bs as)))
    = (set (pg_edges (idPortGraph (as @ bs))) :: ('s, 'a, 'p) edge set)"
    \<comment> \<open>Edges are in different order, but the sets are the same\<close>
  proof -
    have
      " set (pg_edges (seqPortGraphs (swapPortGraph as bs) (swapPortGraph bs as)))
      = set (edgesFromPortMapping (listPorts 0 Out bs @ listPorts (length bs) Out as)
          (Mapping.map_values (\<lambda>k. map edge_from)
            (edgesByOpenTo
              (map2 Edge (map OpenPort (listPorts 0 In as) :: ('s, 'a, 'p) place list)
                (map OpenPort (listPorts (length bs) Out as)) @
               map2 Edge (map OpenPort (listPorts (length as) In bs))
                (map OpenPort (listPorts 0 Out bs)))))
          (Mapping.map_values (\<lambda>k. map edge_to)
            (edgesByOpenFrom
              (map2 Edge (map OpenPort (listPorts 0 In bs) :: ('s, 'a, 'p) place list)
                (map OpenPort (listPorts (length as) Out bs)) @
               map2 Edge (map OpenPort (listPorts (length bs) In as))
                (map OpenPort (listPorts 0 Out as))))))"
      (is "_ = set (edgesFromPortMapping _ ?mappingL ?mappingR)")
      \<comment> \<open>Simplify the sequencing of edges into using two mappings of similar form\<close>
      apply (simp del: listPorts.simps
          add: listPorts_append disconnectFromPlaces_append1
          disconnectFromPlaces_append2 disconnectFromPlaces_map2_edge_those)
      apply (subst (1 2) disconnectFromPlaces_commute)
      apply (simp del: listPorts.simps add: disconnectFromPlaces_map2_edge_those)
      done
    also have "... = set (edgesFromPortMapping (listPorts 0 Out (bs @ as)) ?mappingL ?mappingR)"
      \<comment> \<open>Merge the two invocations of @{const listPorts}\<close>
      by (metis (lifting) listPorts_append add_0_left)
    also have "... = set (edgesFromPortMapping (listPorts 0 Out (bs @ as))
      (Mapping (map (\<lambda>(m, n). (Port Out m ((bs @ as) ! m)
                              , [OpenPort (Port In n ((as @ bs) ! n)) :: ('s, 'a, 'p) place]))
               (map (\<lambda>m. (m, if m \<ge> length bs
                              then m - length bs
                              else m + length as))
                    [0..<length (bs @ as)])))
      (Mapping (map (\<lambda>(m, n). (Port In m ((bs @ as) ! m)
                              , [OpenPort (Port Out n ((as @ bs) ! n)) :: ('s, 'a, 'p) place]))
               (map (\<lambda>m. (m, if m \<ge> length bs
                              then m - length bs
                              else m + length as))
                    [0..<length (bs @ as)]))))"
      (is "_ = set (edgesFromPortMapping _ ?mappingL' ?mappingR')")
      \<comment> \<open>Transform the operations generating the mappings into association lists building ports of
          opposite sides from the same list of labels and using same sequence of indices\<close>
    proof -
      have "?mappingL = ?mappingL'"
        \<comment> \<open>Left mapping maps output ports to corresponding input places.\<close>
      proof -
        have "?mappingL =
          Mapping.map_values (\<lambda>k. map edge_from)
          ( edgesByOpenTo
            ( map2 Edge
              ( map OpenPort ( listPorts 0 In (as @ bs)))
              ( map OpenPort ( listPorts (length bs) Out as
                                @ listPorts 0 Out bs))))"
          \<comment> \<open>Merge @{const map2} and @{const listPorts} applications where possible\<close>
          by (simp del: listPorts.simps add: listPorts_append)
        also have "... =
          Mapping.map_values (\<lambda>k. map edge_from)
           (AList_Mapping.Mapping
             (map (\<lambda>e. (place_port (edge_to e), [e]))
               (map2 Edge (map OpenPort (listPorts 0 In (as @ bs)))
                 (map OpenPort
                   (listPorts (length bs) Out as @
                    listPorts 0 Out bs)))))"
          \<comment> \<open>Since all the edges go to distinct open output port, we can simplify their grouping as
              a single mapping from each output port to its single edge.\<close>
        proof (subst edgesByOpenTo_all_to_distinct)
          let ?es =
            "map2 Edge (map OpenPort (listPorts 0 In (as @ bs)))
                       (map OpenPort (listPorts (length bs) Out as @ listPorts 0 Out bs))"
  
          show "place_open (edge_to e)" if "e \<in> set ?es" for e :: "('s, 'a, 'p) edge"
            using that
            by (smt (verit, best) edge.sel(2) in_set_map2E length_map nth_map place_open_def)
  
          have "OpenPort (Port Out a b) \<in> {}"
             if "(a, b) \<in> set (zip [length bs..<length bs + length as] as)"
            and "(a, b) \<in> set (zip [0..<length bs] bs)"
            for a :: nat and b :: 'a
            using that by (clarsimp elim!: in_set_zipE)
          then have "distinct (map OpenPort (listPorts (length bs) Out as @ listPorts 0 Out bs))"
            by (simp add: distinct_map distinct_zipI1 inj_on_def Ball_def del: empty_iff) safe
          then show "edge_to (?es ! i) \<noteq> edge_to (?es ! j)"
            if "i \<noteq> j" and "i < length ?es" and "j < length ?es"
            for i j
            using that
            apply clarsimp
            apply (subst (asm) nth_eq_iff_index_eq)
            apply (simp_all add: distinct_map distinct_zipI1 inj_on_def)
            done
        qed (rule refl)
        also have "... =
          Mapping ( zip ( map (\<lambda>x. Port Out (fst x) (snd x))
                          ( zip ([length bs..<length bs + length as] @ [0..<length bs]) (as @ bs)))
                        ( map (\<lambda>x. [OpenPort (Port In (fst x) (snd x))])
                          ( zip [0..<length as + length bs] (as @ bs))))"
        \<comment> \<open>Push the @{term "map edge_from"} through to get the mapping as an association list.\<close>
        proof -
          have [simp]:
            " map (\<lambda>x. (place_port (snd x), [fst x])) (zip xs ys)
            = zip (map place_port ys) (map (\<lambda>x. [x]) xs)"
            if "length xs = length ys"
            for xs ys :: "('s, 'a, 'p) place list"
            \<comment> \<open>Important step is pushing a @{const map} that independently transforms the two parts
                of the product through the @{const zip}.\<close>
            (* TODO there is a general rule for map and zip lurking inside this *)
            using that
          proof (induct xs arbitrary: ys)
            case Nil
            then show ?case by simp
          next
            case (Cons x xs')
            then show ?case
              by (clarsimp simp add: Suc_length_conv)
          qed
  
          show ?thesis
            by (simp add: comp_def map_values_Mapping split_beta)
        qed
        also have "... = ?mappingL'"
          \<comment> \<open>Since the two mappings are represented by association lists with distinct keys, they
              are equal if they have the same set of elements.\<close>
        proof (intro Mapping_eqI_distinct_keys)
          show
            " set ( zip ( map (\<lambda>x. Port Out (fst x) (snd x))
                          ( zip ([length bs..<length bs + length as] @ [0..<length bs]) (as @ bs)))
                        ( map (\<lambda>x. [OpenPort (Port In (fst x) (snd x))])
                          ( zip [0..<length as + length bs] (as @ bs)))
                    :: (('s, 'a) port \<times> ('s, 'a, 'p) place list) list)
            = set ( map (\<lambda>(m, n).
                            ( Port Out m ((bs @ as) ! m)
                            , [OpenPort (Port In n ((as @ bs) ! n))]))
                    ( map (\<lambda>m. (m, if m \<ge> length bs
                                     then m - length bs
                                     else m + length as))
                          [0..<length (bs @ as)]))"
            \<comment> \<open>When proving these sets are equal, the index in the list representing the first is
                the natural number that is passed to the outer @{const map} in the second.\<close>
          proof safe
            fix p :: "('s, 'a) port" and es :: "('s, 'a, 'p) place list"
            assume pes: "(p, es) \<in> set (
              zip ( map (\<lambda>x. Port Out (fst x) (snd x))
                        (zip ([length bs..<length bs + length as] @ [0..<length bs]) (as @ bs)))
                  ( map (\<lambda>x. [OpenPort (Port In (fst x) (snd x))])
                        (zip [0..<length as + length bs] (as @ bs))))"

            obtain i
              where i: "i < length as + length bs"
                and p: "p = Port Out (([length bs..<length bs + length as] @ [0..<length bs]) ! i)
                              ((as @ bs) ! i)"
                and es: "es = [OpenPort (Port In i ((as @ bs) ! i))]"
              using pes
              apply (clarsimp simp add: nth_append set_zip)
              apply (case_tac "i < length as")
              apply simp
              apply simp
              done
  
            show "(p, es) \<in> set (
              map (\<lambda>(m, n). (Port Out m ((bs @ as) ! m), [OpenPort (Port In n ((as @ bs) ! n))]))
              ( map (\<lambda>m. (m, if length bs \<le> m then m - length bs else m + length as))
                [0..<length (bs @ as)]))"
              using i by (fastforce simp add: p es nth_append)
          next
            fix p :: "('s, 'a) port" and es :: "('s, 'a, 'p) place list"
            assume pes: "(p, es) \<in> set (
              map (\<lambda>(m, n). (Port Out m ((bs @ as) ! m), [OpenPort (Port In n ((as @ bs) ! n))]))
              ( map (\<lambda>m. (m, if length bs \<le> m then m - length bs else m + length as))
                [0..<length (bs @ as)]))"
  
            obtain i j
              where i: "i < length bs + length as"
                and p: "p = Port Out i ((bs @ as) ! i)"
                and j: "j = (if length bs \<le> i then i - length bs else i + length as)"
                and es: "es = [OpenPort (Port In j ((as @ bs) ! j))]"
              using pes by clarsimp

            have j_less: "j < length as + length bs"
              using i j by (cases "length bs \<le> i") simp_all
            moreover have "p =
              ( map (\<lambda>x. Port Out (fst x) (snd x)) (zip [length bs..<length bs + length as] as)
              @ map (\<lambda>x. Port Out (fst x) (snd x)) (zip [0..<length bs] bs))
              ! j"
              using p j i by (cases "length bs \<le> i") (simp_all add: nth_append less_diff_conv2)
            moreover have "es =
              map (\<lambda>x. [OpenPort (Port In (fst x) (snd x))])
              ( zip [0..<length as + length bs] (as @ bs))
              ! j"
              using j_less es by (simp add: nth_append)
            ultimately show "(p, es) \<in> set (
              zip ( map (\<lambda>x. Port Out (fst x) (snd x))
                        (zip ([length bs..<length bs + length as] @ [0..<length bs]) (as @ bs)))
                  ( map (\<lambda>x. [OpenPort (Port In (fst x) (snd x))])
                        (zip [0..<length as + length bs] (as @ bs))))"
              by (fastforce simp add: set_zip)
          qed
          show "distinct (map fst (zip
            ( map (\<lambda>x. Port Out (fst x) (snd x))
              ( zip ([length bs..<length bs + length as] @ [0..<length bs]) (as @ bs)))
            ( map (\<lambda>x. [OpenPort (Port In (fst x) (snd x))])
              ( zip [0..<length as + length bs] (as @ bs)))))"
            apply (simp add: distinct_map distinct_zipI1 inj_on_def Ball_def)
            apply safe
            apply (clarsimp elim!: in_set_zipE)
            done
          show "distinct (map fst
            ( map (\<lambda>(m, n). (Port Out m ((bs @ as) ! m), [OpenPort (Port In n ((as @ bs) ! n))]))
              ( map (\<lambda>m. (m, if length bs \<le> m then m - length bs else m + length as))
                [0..<length (bs @ as)])))"
            by (simp add: distinct_map inj_on_def)
        qed
        finally show ?thesis .
      qed
      moreover have "?mappingR = ?mappingR'"
        \<comment> \<open>Right mapping maps input ports to corresponding output places.
            The proof is largely similar to the previous one, but it uses @{const edgesByOpenFrom}
            and involves subtly swapping @{term as} with @{term bs} as well as @{const In} with
            @{const Out}, and adjusting theorems used accordingly.
            In addition, the swapped sides swap which (out of ports and places) are given in the
            same order as their associated indices, needing adjustment in terms and sometimes
            simplifying individual steps.\<close>
      proof -
        have "?mappingR =
          Mapping.map_values (\<lambda>k. map edge_to)
          ( edgesByOpenFrom
            ( map2 Edge
              ( map OpenPort ( listPorts 0 In (bs @ as)))
              ( map OpenPort ( listPorts (length as) Out bs
                                @ listPorts 0 Out as))))"
        \<comment> \<open>Merge @{const map2} and @{const listPorts} applications where possible\<close>
        by (simp del: listPorts.simps add: listPorts_append)
        also have "... =
          Mapping.map_values (\<lambda>k. map edge_to)
           (Mapping
             (map (\<lambda>e. (place_port (edge_from e), [e]))
               (map2 Edge (map OpenPort (listPorts 0 In (bs @ as)))
                 (map OpenPort
                   (listPorts (length as) Out bs @
                    listPorts 0 Out as)))))"
          \<comment> \<open>Since all the edges go from distinct open input ports, we can simplify their grouping
              as a single mapping from each input port to its single edge.
              This is rendered simpler than the previous mapping's corresponding case, since we are
              operating on the input ports which are in the same order as their indices.\<close>
        proof (subst edgesByOpenFrom_all_from_distinct)
          let ?es =
            "map2 Edge (map OpenPort (listPorts 0 In (bs @ as)))
                       (map OpenPort (listPorts (length as) Out bs @ listPorts 0 Out as))"
  
          show "place_open (edge_from e)" if "e \<in> set ?es" for e :: "('s, 'a, 'p) edge"
            using that
            by (smt (verit, best) edge.sel(1) in_set_map2E length_map nth_map place_open_def)
  
          show "edge_from (?es ! i) \<noteq> edge_from (?es ! j)"
            if "i \<noteq> j" and "i < length ?es" and "j < length ?es"
            for i j
            using that by clarsimp
        qed (rule refl)
        also have "... =
          Mapping ( zip ( map (\<lambda>x. Port In (fst x) (snd x))
                          ( zip [0..<length bs + length as] (bs @ as)))
                        ( map (\<lambda>x. [OpenPort (Port Out (fst x) (snd x))])
                          ( zip ([length as..<length as + length bs] @ [0..<length as]) (bs @ as))))"
        \<comment> \<open>Push the @{term "map edge_to"} through to get the mapping as an association list.\<close>
        proof -
          have [simp]:
            " map (\<lambda>x. (place_port (fst x), [snd x])) (zip xs ys)
            = zip (map place_port xs) (map (\<lambda>x. [x]) ys)"
            if "length xs = length ys"
            for xs ys :: "('s, 'a, 'p) place list"
            \<comment> \<open>Important step is pushing a @{const map} that independently transforms the two parts
                of the product through the @{const zip}.\<close>
            (* TODO there is a general rule for map and zip lurking inside this *)
            using that
          proof (induct xs arbitrary: ys)
            case Nil
            then show ?case by simp
          next
            case (Cons x xs')
            then show ?case
              by (clarsimp simp add: Suc_length_conv)
          qed
  
          show ?thesis
            by (simp add: comp_def map_values_Mapping split_beta)
        qed
        also have "... = ?mappingR'"
          \<comment> \<open>Since the two mappings are represented by association lists with distinct keys, they
              are equal if they have the same set of elements.\<close>
        proof (intro Mapping_eqI_distinct_keys)
          have
            " set ( zip ( map (\<lambda>x. Port In (fst x) (snd x))
                          ( zip [0..<length bs + length as] (bs @ as)))
                        ( map (\<lambda>x. [OpenPort (Port Out (fst x) (snd x))])
                          ( zip ([length as..<length as + length bs] @ [0..<length as]) (bs @ as)))
                    :: (('s, 'a) port \<times> ('s, 'a, 'p) place list) list)
            = set ( map (\<lambda>(m, n).
                            ( Port In m ((bs @ as) ! m)
                            , [OpenPort (Port Out n ((as @ bs) ! n))]))
                    ( map (\<lambda>m. (m, if m \<ge> length bs
                                     then m - length bs
                                     else m + length as))
                          [0..<length (bs @ as)]))"
            apply safe
             apply (clarsimp simp add: in_set_zip)
             apply (rule_tac x = n in image_eqI)
              apply (case_tac "length bs \<le> n" ; simp add: nth_append less_diff_conv2)
             apply (case_tac "n < length as" ; simp add: nth_append)
            apply clarsimp
            apply (case_tac "x < length bs" ; simp add: in_set_zip)
             apply (rule_tac x = "x" in exI)
             apply (simp add: nth_append)
            apply (rule_tac x = "x" in exI)
            apply (simp add: nth_append less_diff_conv2)
            done
          show
            " set ( zip ( map (\<lambda>x. Port In (fst x) (snd x))
                          ( zip [0..<length bs + length as] (bs @ as)))
                        ( map (\<lambda>x. [OpenPort (Port Out (fst x) (snd x))])
                          ( zip ([length as..<length as + length bs] @ [0..<length as]) (bs @ as)))
                    :: (('s, 'a) port \<times> ('s, 'a, 'p) place list) list)
            = set ( map (\<lambda>(m, n).
                            ( Port In m ((bs @ as) ! m)
                            , [OpenPort (Port Out n ((as @ bs) ! n))]))
                    ( map (\<lambda>m. (m, if m \<ge> length bs
                                     then m - length bs
                                     else m + length as))
                          [0..<length (bs @ as)]))"
            \<comment> \<open>When proving these sets are equal, the index in the list representing the first is
                the natural number that is passed to the outer @{const map} in the second.\<close>
          proof safe
            fix p :: "('s, 'a) port" and es :: "('s, 'a, 'p) place list"
            assume pes: "(p, es) \<in> set (
              zip ( map (\<lambda>x. Port In (fst x) (snd x))
                        (zip [0..<length bs + length as] (bs @ as)))
                  ( map (\<lambda>x. [OpenPort (Port Out (fst x) (snd x))])
                        (zip ([length as..<length as + length bs] @ [0..<length as]) (bs @ as))))"

            obtain i
              where i: "i < length bs + length as"
                and p: "p = Port In i ((bs @ as) ! i)"
                and es: "es = [OpenPort (Port Out (([length as..<length as + length bs] @ [0..<length as]) ! i) ((bs @ as) ! i))]"
              using pes
              apply (clarsimp simp add: nth_append set_zip)
              apply (case_tac "i < length bs")
              apply simp
              apply simp
              done

            show "(p, es) \<in> set (
              map (\<lambda>(m, n). (Port In m ((bs @ as) ! m), [OpenPort (Port Out n ((as @ bs) ! n))]))
              ( map (\<lambda>m. (m, if length bs \<le> m then m - length bs else m + length as))
                [0..<length (bs @ as)]))"
              using i by (fastforce simp add: p es nth_append)
          next
            fix p :: "('s, 'a) port" and es :: "('s, 'a, 'p) place list"
            assume pes: "(p, es) \<in> set (
              map (\<lambda>(m, n). (Port In m ((bs @ as) ! m), [OpenPort (Port Out n ((as @ bs) ! n))]))
              ( map (\<lambda>m. (m, if length bs \<le> m then m - length bs else m + length as))
                [0..<length (bs @ as)]))"

            obtain i j
              where i: "i < length bs + length as"
                and p: "p = Port In i ((bs @ as) ! i)"
                and j: "j = (if length bs \<le> i then i - length bs else i + length as)"
                and es: "es = [OpenPort (Port Out j ((as @ bs) ! j))]"
              using pes by clarsimp

            show "(p, es) \<in> set (
              zip ( map (\<lambda>x. Port In (fst x) (snd x))
                        (zip [0..<length bs + length as] (bs @ as)))
                  ( map (\<lambda>x. [OpenPort (Port Out (fst x) (snd x))])
                        (zip ([length as..<length as + length bs] @ [0..<length as]) (bs @ as))))"
            proof (cases "length bs \<le> i")
              case True
              then show ?thesis
                using p es j i
                apply (clarsimp simp add: set_zip)
                apply (simp add: nth_append)
                apply (intro conjI impI)
                 apply (simp_all add: nth_append)
                 apply (rule_tac x = i in exI)
                 apply (simp add: nth_append)
                done
            next
              case False
              then show ?thesis
                using p es j
                apply (clarsimp simp add: set_zip)
                apply (simp add: nth_append)
                apply (rule_tac x = i in exI)
                apply simp
                done
            qed
          qed
          show "distinct (map fst (zip
            ( map (\<lambda>x. Port In (fst x) (snd x))
              ( zip [0..<length bs + length as] (bs @ as)))
            ( map (\<lambda>x. [OpenPort (Port Out (fst x) (snd x))])
              ( zip ([length as..<length as + length bs] @ [0..<length as]) (bs @ as)))))"
            by (simp add: distinct_map distinct_zipI1 inj_on_def Ball_def)
          show "distinct (map fst
            ( map (\<lambda>(m, n). (Port In m ((bs @ as) ! m), [OpenPort (Port Out n ((as @ bs) ! n))]))
              ( map (\<lambda>m. (m, if length bs \<le> m then m - length bs else m + length as))
                [0..<length (bs @ as)])))"
            by (simp add: distinct_map inj_on_def)
        qed
        finally show ?thesis .
      qed
      ultimately show ?thesis by metis
    qed
    also have "... = set (pg_edges (idPortGraph (as @ bs)))"
      \<comment> \<open>Edges made from these mappings are the edges of the corresponding identity port graph\<close>
    proof safe
      fix e :: "('s, 'a, 'p) edge"
      assume e: "e \<in> set (edgesFromPortMapping (listPorts 0 Out (bs @ as)) ?mappingL' ?mappingR')"

      show "e \<in> set (pg_edges (idPortGraph (as @ bs)))"
        using e
        apply -
        apply (erule edgesFromPortMapping_in_set_nthE)
        apply (simp add: comp_def)
        apply (drule map_of_SomeD)+
        apply (simp del: set_upt)
        apply (subst (asm) (1 2) set_map[symmetric])
        apply (subst (asm) (1 2) in_set_conv_nth)
        apply (case_tac "length bs \<le> i" ; clarsimp del: pair_imageI intro!: pair_imageI simp add: in_set_zip)
         apply (rule_tac x = "i - length bs" in exI)
         apply (simp add: comp_def)
         apply (intro conjI)
           apply (subst nth_zip ; simp)
          apply (subst nth_zip ; simp)
         apply simp
        apply (rule_tac x = "i + length as" in exI)
        apply (simp add: comp_def)
        done
    next
      fix e :: "('s, 'a, 'p) edge"
      assume "e \<in> set (pg_edges (idPortGraph (as @ bs)))"
      then obtain n
        where e: "e = Edge (OpenPort (Port In n ((as @ bs) ! n))) (OpenPort (Port Out n ((as @ bs) ! n)))"
          and n: "n < length as + length bs"
        by (fastforce simp add: in_set_zip)

      show "e \<in> set (edgesFromPortMapping (listPorts 0 Out (bs @ as)) ?mappingL' ?mappingR')"
      proof (cases "n < length as")
        case True

        show ?thesis
        proof (intro edgesFromPortMapping_setI)
          let ?p = "Port Out (n + length bs) ((bs @ as) ! (n + length bs))"
          let ?x = "OpenPort (Port In n ((as @ bs) ! n))"
          let ?xs = "[?x]"
          let ?y = "OpenPort (Port Out n ((as @ bs) ! n))"
          let ?ys = "[?y]"

          show "?p \<in> set (listPorts 0 Out (bs @ as))"
            using True listPorts_length nth_listPorts in_set_conv_nth
            by (metis (no_types, lifting) add.commute add_0 add_less_cancel_left length_append)
          show "Mapping.lookup ?mappingL' (portSetSide Out ?p) = Some ?xs"
            using True
            apply (clarsimp simp add: map_of_map_key_value comp_def)
            apply (rule map_of_is_SomeI)
             apply (simp add: comp_def distinct_map inj_on_def)
            apply auto
            done
          show "Mapping.lookup ?mappingR' (portSetSide In ?p) = Some ?ys"
            using True
            apply (clarsimp simp add: map_of_map_key_value comp_def)
            apply (rule map_of_is_SomeI)
             apply (simp add: comp_def distinct_map inj_on_def)
            apply auto
            done
          show "?x \<in> set ?xs" by simp
          show "?y \<in> set ?ys" by simp
          show "e = Edge ?x ?y" using e .
        qed
      next
        case False
        then have n_as [simp]: "n - length as < length bs"
          using n by simp

        show ?thesis
        proof (intro edgesFromPortMapping_setI)
          let ?p = "Port Out (n - length as) ((bs @ as) ! (n - length as))"
          let ?x = "OpenPort (Port In n ((as @ bs) ! n))"
          let ?xs = "[?x]"
          let ?y = "OpenPort (Port Out n ((as @ bs) ! n))"
          let ?ys = "[?y]"

          show "?p \<in> set (listPorts 0 Out (bs @ as))"
            using n
            apply (clarsimp simp add: in_set_zip nth_append)
            apply (rule pair_imageI)
            apply (simp add: in_set_zip)
            apply (rule_tac x = "n - length as" in exI)
            apply (simp add: nth_append)
            done
          show "Mapping.lookup ?mappingL' (portSetSide Out ?p) = Some ?xs"
            using False n
            apply (simp add: comp_def)
            apply (subst map_of_map_key_value)
              apply (simp add: inj_on_def)
             apply simp
            apply (rule map_of_is_SomeI)
             apply (simp add: comp_def)
            apply simp
            apply (rule_tac x = "n - length as" in image_eqI)
             apply (simp add: Nat.le_diff_conv2)
            apply simp
            done
          show "Mapping.lookup ?mappingR' (portSetSide In ?p) = Some ?ys"
            using False n
            apply (simp add: comp_def)
            apply (subst map_of_map_key_value)
              apply (simp add: inj_on_def)
             apply simp
            apply (rule map_of_is_SomeI)
             apply (simp add: comp_def)
            apply simp
            apply (rule_tac x = "n - length as" in image_eqI)
             apply (simp add: Nat.le_diff_conv2)
            apply simp
            done
          show "?x \<in> set ?xs" by simp
          show "?y \<in> set ?ys" by simp
          show "e = Edge ?x ?y" using e .
        qed
      qed
    qed
    finally show ?thesis .
  qed
  show "set (pg_ports (seqPortGraphs (swapPortGraph as bs) (swapPortGraph bs as))) =
        set (pg_ports (idPortGraph (as @ bs)))"
  proof -
    have [simp]:
      "{x \<in> set (listPorts 0 In (as @ bs)). port.side x \<noteq> Out} = set (listPorts 0 In (as @ bs))"
      "{x \<in> set (listPorts 0 Out (bs @ as)). port.side x \<noteq> Out} = {}"
      "{x \<in> set (listPorts 0 In (bs @ as)). port.side x \<noteq> In \<and> port.side x \<noteq> Out} = {}"
      "{x \<in> set (listPorts 0 Out (as @ bs)). port.side x \<noteq> In \<and> port.side x \<noteq> Out} = {}"
      by fastforce+
    show ?thesis
      by (simp del: listPorts.simps)
  qed
  show "distinct (pg_nodes (idPortGraph (as @ bs)))"
    by simp
  show "distinct (pg_edges (idPortGraph (as @ bs)))"
    using port_graph.edges_distinct port_graph_flow.axioms(1) port_graph_flow_idPortGraph by blast
  show "distinct (pg_ports (idPortGraph (as @ bs)))"
    using port_graph.ports_distinct port_graph_flow.axioms(1) port_graph_flow_idPortGraph by blast
qed

subsection\<open>Identity as Sequential Inverse\<close>

text\<open>
  There exists a particularly simple case of @{const seqInterfaceEdges}, where the result is just
  edges constructed from two known place lists.
  This is when the edges of the two input port graphs are constructed by @{const map2} from lists of
  places each (list of origins and list of destinations) that are exactly the connections to the
  interface ports.
  The two place lists of each port graph need to be of equal length and the interface ports must be
  distinct, together meaning that the edges connect exactly one place of each port graph to each
  interface port.
\<close>
lemma edgesFromPortMapping_simple: (* TODO is there a better name? *)
  assumes "length xs1 = length xs2"
      and "length ys1 = length ys2"
      and "xs2 = map OpenPort ps"
      and "ys1 = map OpenPort (map (portSetSide In) ps)"
      and "\<And>p. p \<in> set ps \<Longrightarrow> port.side p = Out"
      and "distinct ps"
  shows
    " edgesFromPortMapping ps
        (Mapping.map_values (\<lambda>k. map edge_from) (edgesByOpenTo (map2 Edge xs1 xs2)))
        (Mapping.map_values (\<lambda>k. map edge_to) (edgesByOpenFrom (map2 Edge ys1 ys2))) =
      map2 Edge xs1 ys2"
  using assms(1,2,5,6)
  unfolding assms(3) assms(4) length_map
proof (induct ps arbitrary: xs1 ys2)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)

  obtain x xs where "xs1 = x # xs" and "length xs = length ps"
    using Cons(2) length_Suc_conv by metis
  note xs = this

  obtain y ys where "ys2 = y # ys" and "length ys = length ps"
    using Cons(3) length_Suc_conv by metis
  note ys = this

  have "p \<notin> Mapping.keys (edgesByOpenTo (map2 Edge xs (map OpenPort ps)))"
    using Cons.prems(4) xs(2) edgesByOpenTo_simple_keys by (metis distinct.simps(2))
  moreover have "Mapping.lookup (edgesByOpenTo (map2 Edge xs (map OpenPort ps))) p = None"
    using calculation keys_dom_lookup by fastforce
  moreover have "portSetSide In p \<notin> Mapping.keys (edgesByOpenFrom (map2 Edge (map OpenPort (map (portSetSide In) ps)) ys))"
    using Cons.prems(3,4) ys(2)
    apply (simp add: edgesByOpenFrom_simple_keys comp_def del: map_map)
    apply (metis (no_types, opaque_lifting) imageE portSetSide_absorb portSetSide_same)
    done
  moreover have "Mapping.lookup (edgesByOpenFrom (map2 Edge (map (OpenPort \<circ> portSetSide In) ps) ys)) (portSetSide In p) = None"
    using calculation keys_dom_lookup by fastforce
  ultimately show ?case
    using Cons(1,4,5) xs ys
    apply (simp add: lookup_map_default lookup_map_values)
    apply (simp add: map_default_def default_def lookup_default_def)

    apply (rule_tac a1 = p and ps1 = ps in subst[OF edgesFromPortMapping_deleteL[symmetric]])
     apply fastforce
    apply (rule_tac a1 = "portSetSide In p" and ps1 = ps in subst[OF edgesFromPortMapping_deleteR[symmetric]])
     apply (metis (no_types, opaque_lifting) imageE portSetSide_absorb portSetSide_same)

    apply (simp add: delete_map_values delete_update)

    done
qed

text\<open>Sequencing two identity port graphs is the same as one of them, making it its own inverse.\<close>
lemma seqPortGraphs_id_inverse:
  notes listPorts.simps[simp del]
  shows "seqPortGraphs (idPortGraph a) (idPortGraph a) = idPortGraph a"
proof -
  have "pg_nodes (seqPortGraphs (idPortGraph a) (idPortGraph a)) = pg_nodes (idPortGraph a)"
    by simp
  moreover have "pg_edges (seqPortGraphs (idPortGraph a) (idPortGraph a)) = pg_edges (idPortGraph a)"
  proof -
    have "distinct (map2 Edge (map OpenPort (listPorts 0 In a)) (map OpenPort (listPorts 0 Out a)))"
      by (simp add: distinct_map distinct_zipI1)
    moreover have "\<And>p. p \<in> set (listPorts 0 Out a) \<Longrightarrow> port.side p = Out"
      by (metis in_set_map2E listPorts.simps port.sel(1))
    ultimately show ?thesis
      apply (simp add: listPorts_append disconnectFromPlaces_map2_edge_those)
      apply (subst edgesFromPortMapping_simple)
           apply simp_all
      apply assumption
      done
  qed
  moreover have "pg_ports (seqPortGraphs (idPortGraph a) (idPortGraph a)) = pg_ports (idPortGraph a)"
  proof -
    have "filter (\<lambda>x. port.side x \<noteq> Out) (listPorts 0 In a) = listPorts 0 In a"
      by (smt (verit, ccfv_threshold) filter_id_conv filter_port_side_listPorts(1) in_out_distinct)
    moreover have "filter (\<lambda>x. port.side x \<noteq> Out) (listPorts 0 Out a) = []"
      by (metis empty_filter_conv filter_id_conv filter_port_side_listPorts(1))
    moreover have "filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out) (listPorts 0 In a) = []"
      by (smt (verit, best) empty_filter_conv filter_port_side_listPorts(2))
    moreover have "filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out) (listPorts 0 Out a) = []"
      by (metis (no_types, lifting) calculation(2) empty_filter_conv)
    moreover note [simp] = calculation

    show ?thesis
      by simp
  qed
  ultimately show ?thesis
    using port_graph.expand by blast
qed

subsection\<open>Identity as Sequential Unit\<close>

text\<open>
  Sequencing an identity port graph to the left of any other port graph with flow is equivalent to
  it (making identity the left unit of sequencing) if the identity is on that port graph's open
  input ports.
\<close>
lemma seqPortGraphs_unitL_pgEquiv:
  fixes x :: "('s :: side_in_out, 'a, 'p, 'l) port_graph"
  assumes "port_graph_flow x"
      and "set (filter (\<lambda>x. port.side x = In) (pg_ports x)) = set (listPorts 0 In as)"
    shows "seqPortGraphs (idPortGraph as) x \<approx> x" (is "seqPortGraphs ?idg x \<approx> x")
proof -
  show "seqPortGraphs (idPortGraph as) x \<approx> x"
  proof (intro pgEquivI)
    show pg_x: "port_graph x"
      using assms port_graph_flow.axioms(1) by blast
    show "port_graph (seqPortGraphs (idPortGraph as) x)"
      using assms port_graph_flow_seqPortGraphs port_graph_flow_idPortGraph pg_disjoint_trivialI1
      by (metis idPortGraph.simps port_graph.sel(1) port_graph_flow.axioms(1))
    show "set (pg_ports (seqPortGraphs (idPortGraph as) x)) = set (pg_ports x)"
    proof -
      have "{x \<in> set (listPorts 0 In as). port.side x \<noteq> Out} = set (listPorts 0 In as)"
        by fastforce
      moreover have "{x \<in> set (listPorts 0 Out as). port.side x \<noteq> Out} = {}"
        by fastforce
      moreover have
        " shiftPort
            (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (listPorts 0 In as)) +
                 length (filter (\<lambda>p. port.side p = s) (listPorts 0 Out as))) `
          {xa \<in> set (pg_ports x). port.side xa \<noteq> In \<and> port.side xa \<noteq> Out}
        = {xa \<in> set (pg_ports x). port.side xa \<noteq> In \<and> port.side xa \<noteq> Out}"
        apply (intro set_eqI iffI)
        apply (clarsimp simp del: listPorts.simps)
        apply (metis (mono_tags, lifting) add_cancel_right_left filter_port_side_listPorts(2) list.size(3) port.collapse shiftPort_def)
        apply (clarsimp simp del: listPorts.simps)
        by (smt (verit) add_0 filter_port_side_listPorts(2) image_iff list.size(3) mem_Collect_eq port.collapse shiftPort_def)
      moreover note [simp] = calculation

      have "set (pg_ports x) =
        {xa \<in> set (pg_ports x). port.side xa = In} \<union>
        {xa \<in> set (pg_ports x). port.side xa = Out} \<union>
        {xa \<in> set (pg_ports x). port.side xa \<noteq> In \<and> port.side xa \<noteq> Out}"
        by blast
      then show ?thesis
        using assms(2) by (simp del: listPorts.simps) blast
    qed
    show "pgEquiv_witness id id (seqPortGraphs (idPortGraph as) x) x"
      unfolding pgEquiv_witness_id
    proof
      show "set (pg_nodes (seqPortGraphs (idPortGraph as) x)) = set (pg_nodes x)"
        by simp
      show "set (pg_edges (seqPortGraphs (idPortGraph as) x)) = set (pg_edges x)"
      proof -
        have seq:
          " set (seqInterfaceEdges (idPortGraph as) x) =
            set (filter fromOpenIn (pg_edges x))"
        proof (intro set_eqI iffI)
          fix e
          assume "e \<in> set (seqInterfaceEdges (idPortGraph as) x)"
          then obtain f g :: "('s, 'a, 'p) edge" and p :: "('s, 'a) port"
            where "edge_from e = edge_from f" and "f \<in> set (pg_edges ?idg)"
              and "edge_to e = edge_to g" and "g \<in> set (pg_edges x)"
              and "edge_to f = OpenPort (portSetSide Out p)"
              and "edge_from g = OpenPort (portSetSide In p)"
              and "port.side p = Out"
            using seqInterfaceEdges_setD by metis
          note ef = this

          have "edge_from f = OpenPort (portSetSide In p)"
            using ef(2,5) by (cases p, clarsimp simp add: in_set_zip)
          then have "e = g"
            using ef(1,3,6) by (simp add: edge.expand)
          moreover have "fromOpenIn g"
            using ef(6) by (simp add: fromOpenIn_def)
          ultimately show "e \<in> set (filter fromOpenIn (pg_edges x))"
            using ef(4) by simp
        next
          fix e
          assume e: "e \<in> set (filter fromOpenIn (pg_edges x))"

          let ?partner = "Edge (OpenPort (portSetSide In (place_port (edge_from e)))) (OpenPort (portSetSide Out (place_port (edge_from e))))"

          have in_id: "?partner \<in> set (pg_edges (idPortGraph as))"
          proof -
            have "place_port (edge_from e) \<in> set (filter (\<lambda>x. port.side x = In) (pg_ports x))"
              using pg_x e port_graph.edge_from_pg by fastforce
            then have "place_port (edge_from e) \<in> set (listPorts 0 In as)"
              using assms by metis
            then obtain n where "listPorts 0 In as ! n = place_port (edge_from e)" and "n < length (listPorts 0 In as)"
              by (metis in_set_conv_nth listPorts_length)
            note n = this

            have "pg_edges (idPortGraph as) ! n = ?partner"
              using n by simp (metis portSetSide.simps)
            moreover have "n < length (pg_edges (idPortGraph as))"
              using n(2) by simp
            ultimately show ?thesis
              by (metis in_set_conv_nth)
          qed

          show "e \<in> set (seqInterfaceEdges (idPortGraph as) x)"
            apply (rule seqInterfaceEdges_setI[where a = ?partner and b = e])
            using port_graph_flow_idPortGraph apply blast
            apply (simp add: assms)
            using e place.collapse(2) apply fastforce
            using in_id apply blast
            apply (rule refl)
            using e apply simp
             apply simp
            using e place.collapse(2) apply (fastforce simp add: fromOpenIn_def)
            done
        qed

        have disc_id:
          " disconnectFromPlaces
              (map OpenPort (filter (\<lambda>x. port.side x = Out) (pg_ports (idPortGraph as))))
              (pg_edges (idPortGraph as)) = []"
          by (simp del: listPorts.simps add: disconnectFromPlaces_map2_edge_those)

        have shift_is_ident:
          "shiftOpenInEdge
              (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports (idPortGraph as))))
              (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports (idPortGraph as))))
          = (\<lambda>x. x)" (is "shiftOpenInEdge ?f ?g = (\<lambda>x. x)")
        proof
          fix e :: "('b, 'c, 'd) edge"

          have "shiftOpenPlace ?f (edge_from e) = edge_from e"
            apply (cases "place_open (edge_from e)")
            apply (cases "place_side (edge_from e) = In")
            apply simp
            apply (cases "place_side (edge_from e) = Out")
            apply simp
            apply simp
             apply (smt (verit, del_insts) add_cancel_right_left filter_append filter_port_side_listPorts(2) idPortGraph.simps length_append list.size(3)
                place.collapse(2) port.collapse port_graph.sel(3) shiftOpenPlace.simps(2) shiftPort_def)
            apply simp
            done
          moreover have "shiftOpenPlace ?g (edge_to e) = edge_to e"
            apply (cases "place_open (edge_to e)")
            apply (cases "place_side (edge_to e) = In")
            apply simp
            apply (cases "place_side (edge_from e) = Out")
            apply simp
              apply (smt (verit, del_insts) add_cancel_right_left filter_append filter_port_side_listPorts(2) idPortGraph.simps length_append list.size(3) place.collapse(2)
                port.collapse port_graph.sel(3) shiftOpenPlace.simps(2) shiftPort_def)
            apply simp
             apply (smt (verit, del_insts) add_cancel_right_left filter_append filter_port_side_listPorts(2) idPortGraph.simps length_append list.size(3) place.collapse(2)
                port.collapse port_graph.sel(3) shiftOpenPlace.simps(2) shiftPort_def)
            apply simp
            done
          ultimately show "shiftOpenInEdge ?f ?g e = e"
            by (simp add: shiftOpenInEdge_def)
        qed

        show ?thesis
          apply (simp only: seqPortGraphs.simps port_graph.sel)
          apply (subst disc_id)
          apply (simp only: set_append append_Nil)
          apply (subst seq)
          apply (subst port_graph_flow.disconnect_in)
           apply (rule assms)
          apply (simp add: shift_is_ident)
          apply blast
          done
      qed
    qed
  qed
qed

text\<open>
  Sequencing an identity port graph to the right of any other port graph with flow is equivalent to
  it (making identity the right unit of sequencing) if the identity is on that port graph's open
  output ports.
\<close>
lemma seqPortGraphs_unitR_pgEquiv:
  fixes x :: "('s :: side_in_out, 'a, 'p, 'l) port_graph"
  assumes "port_graph_flow x"
      and "set (filter (\<lambda>x. port.side x = Out) (pg_ports x)) = set (listPorts 0 Out as)"
    shows "seqPortGraphs x (idPortGraph as) \<approx> x" (is "seqPortGraphs x ?idg \<approx> x")
proof -
  show "seqPortGraphs x (idPortGraph as) \<approx> x"
  proof (intro pgEquivI)
    show pg_x: "port_graph x"
      using assms port_graph_flow.axioms(1) by blast
    show "port_graph (seqPortGraphs x (idPortGraph as))"
      using assms port_graph_flow_seqPortGraphs port_graph_flow_idPortGraph pg_disjoint_trivialI2
      by (metis idPortGraph.simps port_graph.sel(1) port_graph_flow.axioms(1))
    show "set (pg_ports (seqPortGraphs x (idPortGraph as))) = set (pg_ports x)"
    proof -
      have "{x \<in> set (listPorts 0 In as). port.side x \<noteq> In \<and> port.side x \<noteq> Out} = {}"
        by fastforce
      moreover have "{x \<in> set (listPorts 0 Out as). port.side x \<noteq> In \<and> port.side x \<noteq> Out} = {}"
        by fastforce
      moreover note [simp] = calculation

      have "set (pg_ports x) =
        {xa \<in> set (pg_ports x). port.side xa = In} \<union>
        {xa \<in> set (pg_ports x). port.side xa = Out} \<union>
        {xa \<in> set (pg_ports x). port.side xa \<noteq> In \<and> port.side xa \<noteq> Out}"
        by blast
      then show ?thesis
        using assms(2) by (simp del: listPorts.simps) blast
    qed
    show "pgEquiv_witness id id (seqPortGraphs x (idPortGraph as)) x"
      unfolding pgEquiv_witness_id
    proof
      show "set (pg_nodes (seqPortGraphs x (idPortGraph as))) = set (pg_nodes x)"
        by simp
      show "set (pg_edges (seqPortGraphs x (idPortGraph as))) = set (pg_edges x)"
      proof -
        have seq:
          " set (seqInterfaceEdges x (idPortGraph as)) =
            set (filter toOpenOut (pg_edges x))"
        proof (intro set_eqI iffI)
          fix e
          assume "e \<in> set (seqInterfaceEdges x (idPortGraph as))"
          then obtain f g :: "('s, 'a, 'p) edge" and p :: "('s, 'a) port"
            where "edge_from e = edge_from f" and "f \<in> set (pg_edges x)"
              and "edge_to e = edge_to g" and "g \<in> set (pg_edges ?idg)"
              and "edge_to f = OpenPort (portSetSide Out p)"
              and "edge_from g = OpenPort (portSetSide In p)"
              and "port.side p = Out"
            using seqInterfaceEdges_setD by metis
          note ef = this

          have "edge_to g = OpenPort (portSetSide Out p)"
            using ef(4,6) by (cases p, clarsimp simp add: in_set_zip)
          then have "e = f"
            using ef(1,3,5) by (simp add: edge.expand)
          moreover have "toOpenOut f"
            using ef(5) by (simp add: toOpenOut_def)
          ultimately show "e \<in> set (filter toOpenOut (pg_edges x))"
            using ef(2) by simp
        next
          fix e
          assume e: "e \<in> set (filter toOpenOut (pg_edges x))"

          let ?partner = "Edge (OpenPort (portSetSide In (place_port (edge_to e)))) (OpenPort (portSetSide Out (place_port (edge_to e))))"

          have in_id: "?partner \<in> set (pg_edges (idPortGraph as))"
          proof -
            have "place_port (edge_to e) \<in> set (filter (\<lambda>x. port.side x = Out) (pg_ports x))"
              using pg_x e port_graph.edge_to_pg by fastforce
            then have "place_port (edge_to e) \<in> set (listPorts 0 Out as)"
              using assms by metis
            then obtain n where "listPorts 0 Out as ! n = place_port (edge_to e)" and "n < length (listPorts 0 Out as)"
              by (metis distinct_Ex1 distinct_listPorts listPorts_length)
            note n = this

            have "pg_edges (idPortGraph as) ! n = ?partner"
              using n by simp (metis portSetSide.simps)
            moreover have "n < length (pg_edges (idPortGraph as))"
              using n(2) by simp
            ultimately show ?thesis
              by (metis in_set_conv_nth)
          qed

          show "e \<in> set (seqInterfaceEdges x (idPortGraph as))"
            apply (rule seqInterfaceEdges_setI[where a = e and b = ?partner])
            apply (simp add: assms)
            using port_graph_flow_idPortGraph apply blast
            apply (rule refl)
            using e apply simp
            using e place.collapse(2) apply fastforce
            using in_id apply blast
            defer apply simp
            using e place.collapse(2) apply (fastforce simp add: fromOpenIn_def)
            done
        qed

        have disc_id:
          " disconnectFromPlaces
              (map OpenPort (filter (\<lambda>x. port.side x = In) (pg_ports (idPortGraph as))))
              (pg_edges (idPortGraph as)) = []"
          by (simp del: listPorts.simps add: disconnectFromPlaces_map2_edge_those)

        show ?thesis
          apply (simp only: seqPortGraphs.simps port_graph.sel)
          apply (subst disc_id)
          apply (simp only: set_append append_Nil)
          apply (subst seq)
          apply (subst port_graph_flow.disconnect_out)
           apply (rule assms)
          apply simp
          apply blast
          done
      qed
    qed
  qed
qed

subsection\<open>Juxtaposed Identities\<close>

text\<open>Juxtaposing two identity port graphs produces a combined identity port graph.\<close>
lemma juxtapose_id_merge:
  notes listPorts.simps[simp del]
  shows "juxtapose (idPortGraph xs) (idPortGraph ys) \<approx> idPortGraph (xs @ ys)" (is "juxtapose ?idX ?idY \<approx> ?idXY")
proof (rule pgEquiv_permute)
  show "port_graph (juxtapose (idPortGraph xs) (idPortGraph ys))"
    using port_graph_flow_idPortGraph port_graph_flow_juxtapose
    by (metis pg_disjoint_trivialI1 idPortGraph.simps port_graph.sel(1) port_graph_flow.axioms(1))
  show "set (pg_nodes (juxtapose (idPortGraph xs) (idPortGraph ys))) = set (pg_nodes (idPortGraph (xs @ ys)))"
    by simp
  show "set (pg_edges (juxtapose ?idX ?idY)) = set (pg_edges ?idXY)"
  proof -
    have
      " pg_edges (juxtapose ?idX ?idY)
      = pg_edges (idPortGraph xs) @
        map (shiftOpenInEdge
            (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports ?idX)))
            (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports ?idX))))
          (pg_edges (idPortGraph ys))"
      by simp
    moreover have
      " map (shiftOpenInEdge
            (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports ?idX)))
            (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports ?idX))))
          (pg_edges (idPortGraph ys))
      = map (shiftOpenInEdge
            (\<lambda>s. length (filter (\<lambda>x. port.side x = In) (pg_ports ?idX)))
            (\<lambda>s. length (filter (\<lambda>x. port.side x = Out) (pg_ports ?idX))))
          (pg_edges (idPortGraph ys))"
      by (clarsimp simp add: in_set_zip shiftOpenInEdge_def shiftPort_def)
    ultimately have
      " pg_edges (juxtapose ?idX ?idY)
      = pg_edges (idPortGraph xs) @
        map (shiftOpenInEdge
            (\<lambda>s. length (filter (\<lambda>x. port.side x = In) (pg_ports ?idX)))
            (\<lambda>s. length (filter (\<lambda>x. port.side x = Out) (pg_ports ?idX))))
          (pg_edges (idPortGraph ys))"
      by metis
    moreover have
      "length (filter (\<lambda>x. port.side x = In) (pg_ports ?idX)) = length xs"
      "length (filter (\<lambda>x. port.side x = Out) (pg_ports ?idX)) = length xs"
      by simp_all
    ultimately have LHS:
      " pg_edges (juxtapose ?idX ?idY)
      = pg_edges (idPortGraph xs) @
        map (shiftOpenInEdge (\<lambda>s :: 'a. length xs) (\<lambda>s :: 'a. length xs)) (pg_edges (idPortGraph ys))"
      by metis

    have RHS:
      " pg_edges ?idXY
      = map2 Edge (map OpenPort (listPorts 0 In (xs @ ys))) (map OpenPort (listPorts 0 Out (xs @ ys)))"
      by simp

    show ?thesis
      apply (subst LHS, subst RHS)
      unfolding idPortGraph.simps port_graph.sel map_shiftOpenInEdge_map2 shiftOpenPlace.simps shiftOpenPlace_listPorts
      by (simp add: listPorts_append)
  qed
  show "set (pg_ports (juxtapose ?idX ?idY)) = set (pg_ports ?idXY)"
    by (simp add: listPorts_append) blast
  show "distinct (pg_nodes (idPortGraph (xs @ ys)))"
    by simp
  show "distinct (pg_edges (idPortGraph (xs @ ys)))"
    by (clarsimp simp add: distinct_map distinct_zipI1 inj_on_def)
  show "distinct (pg_ports (idPortGraph (xs @ ys)))"
    by simp
qed

subsection\<open>Empty Identity as Juxtaposition Unit\<close>

text\<open>Identity port graph on the empty resource acts as identity for juxtaposition.\<close>
text\<open>
  Juxtaposing an identity port graph to the left or right of any other port graph is equal to it
  (making empty identity the left and right unit of juxtaposition).
  This has no requirements on the port graph, nor is it just an equivalence.
\<close>
lemma
  shows juxtapose_unitL: "juxtapose (idPortGraph []) x = x"
    and juxtapose_unitR: "juxtapose x (idPortGraph []) = x"
  by simp_all

subsection\<open>Fork-End Comonoid\<close>

text\<open>
  Fork and end port graphs satisfy the rules of commutative comonoids:
  \<^item> Fork followed by end juxtaposed with identity (in either order) is equal to identity.
  \<^item> Fork followed by another juxtaposed with identity is the same no matter the parallel order.
  \<^item> Fork followed by swap is equivalent to just the fork.
\<close>
lemma
  notes [simp] = map_default_def default_def map_entry_code empty_Mapping update_Mapping map_values_Mapping
  shows forkPortGraph_unitL:
    "seqPortGraphs (forkPortGraph x) (juxtapose (endPortGraph [x]) (idPortGraph [x])) = idPortGraph [x]"
    and forkPortGraph_unitR:
    "seqPortGraphs (forkPortGraph x) (juxtapose (idPortGraph [x]) (endPortGraph [x])) = idPortGraph [x]"
    and forkPortGraph_assoc:
    " seqPortGraphs (forkPortGraph x) (juxtapose (idPortGraph [x]) (forkPortGraph x))
    = seqPortGraphs (forkPortGraph x) (juxtapose (forkPortGraph x) (idPortGraph [x]))"
  by (simp_all add: disconnectFromPlaces_def)

lemma forkPortGraph_comm:
  "seqPortGraphs (forkPortGraph x) (swapPortGraph [x] [x]) \<approx> forkPortGraph x"
proof (rule pgEquiv_permute)
  note [simp] = map_default_def default_def map_entry_code empty_Mapping update_Mapping map_values_Mapping

  show "port_graph (seqPortGraphs (forkPortGraph x) (swapPortGraph [x] [x]))"
    using port_graph_flow_seqPortGraphs port_graph_flow_forkPortGraph port_graph_flow_swapPortGraph
    by (metis pg_disjoint_trivialI1 forkPortGraph.simps port_graph.sel(1) port_graph_flow.axioms(1))
  show
    " set (pg_nodes (seqPortGraphs (forkPortGraph x) (swapPortGraph [x] [x])))
    = set (pg_nodes (forkPortGraph x))"
    by simp
  show
    " set (pg_edges (seqPortGraphs (forkPortGraph x) (swapPortGraph [x] [x])))
    = set (pg_edges (forkPortGraph x))"
    by (simp add: disconnectFromPlaces_def) blast
  show "set (pg_ports (seqPortGraphs (forkPortGraph x) (swapPortGraph [x] [x]))) =
    set (pg_ports (forkPortGraph x))"
    by simp
  show "distinct (pg_nodes (forkPortGraph x))"
    by simp
  show "distinct (pg_edges (forkPortGraph x))"
    by simp
  show "distinct (pg_ports (forkPortGraph x))"
    by simp
qed

end
