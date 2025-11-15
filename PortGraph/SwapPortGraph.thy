theory SwapPortGraph
  imports PortGraph
begin

section\<open>Swap Port Graph\<close>

text\<open>
  Swap port graph has no nodes, it only connects input ports directly to output ports like identity
  but in two swapped clusters.
\<close>
fun swapPortGraph :: "('a \<times> 'el) list \<Rightarrow> ('a \<times> 'el) list \<Rightarrow> ('s :: side_in_out, 'a, 'p, 'nl, 'el) port_graph"
  where "swapPortGraph a b =
  PGraph
    []
    ( map3 Edge (map OpenPort (listPorts 0 In (map fst a)))
                (map OpenPort (listPorts (length b) Out (map fst a)))
                (map snd a)
    @ map3 Edge (map OpenPort (listPorts (length a) In (map fst b)))
                (map OpenPort (listPorts 0 Out (map fst b)))
                (map snd b))
    (listPorts 0 In (map fst a @ map fst b) @ listPorts 0 Out (map fst b @ map fst a))"

lemma port_graph_flow_swapPortGraph:
  "port_graph_flow (swapPortGraph a b)" (is "port_graph_flow ?G")
proof unfold_locales
  fix e
  assume e_in: "e \<in> set (pg_edges ?G)"
  then consider
      "e \<in> set (map3 Edge (map OpenPort (listPorts 0 In (map fst a))) (map OpenPort (listPorts (length b) Out (map fst a))) (map snd a))"
    | "e \<in> set (map3 Edge (map OpenPort (listPorts (length a) In (map fst b))) (map OpenPort (listPorts 0 Out (map fst b))) (map snd b))"
    by fastforce
  then consider
      (A) i where "i < length a" "e = Edge (OpenPort (Port In i (map fst a ! i))) (OpenPort (Port Out (i + length b) (map fst a ! i))) (map snd a ! i)"
    | (B) i where "i < length b" "e = Edge (OpenPort (Port In (i + length a) (map fst b ! i))) (OpenPort (Port Out i (map fst b ! i))) (map snd b ! i)"
    by cases (fastforce elim!: in_set_map3E)+
  then have "edge_from e \<in> set (pgraphPlaces ?G) \<and> edge_to e \<in> set (pgraphPlaces ?G)"
  proof cases
    case A
    moreover have
      " OpenPort (Port In i (fst (a ! i)))
      \<in> OpenPort ` set (listPorts 0 In (map fst a @ map fst b))"
    proof (rule image_eqI)
      show "OpenPort (Port In i (fst (a ! i))) = OpenPort (listPorts 0 In (map fst a @ map fst b) ! i)"
        using A(1) by (simp add: nth_append)
      show "listPorts 0 In (map fst a @ map fst b) ! i \<in> set (listPorts 0 In (map fst a @ map fst b))"
        using A(1) by (metis length_append length_map listPorts_length nth_mem trans_less_add1)
    qed
    moreover have
      " OpenPort (Port Out (i + length b) (fst (a ! i)))
      \<in> OpenPort ` set (listPorts 0 Out (map fst b @ map fst a))"
    proof (rule image_eqI)
      show "OpenPort (Port Out (i + length b) (fst (a ! i))) = OpenPort (listPorts 0 Out (map fst b @ map fst a) ! (i + length b))"
        using A(1) by (simp add: nth_append)
      show "listPorts 0 Out (map fst b @ map fst a) ! (i + length b) \<in> set (listPorts 0 Out (map fst b @ map fst a))"
        using A(1) by (metis add.commute add_less_mono1 length_append length_map listPorts_length nth_mem)
    qed
    ultimately show ?thesis
      by (simp del: listPorts.simps) blast
  next
    case B
    moreover have
      " OpenPort (Port In (i + length a) (fst (b ! i)))
      \<in> OpenPort ` set (listPorts 0 In (map fst a @ map fst b))"
    proof (rule image_eqI)
      show "OpenPort (Port In (i + length a) (fst (b ! i))) = OpenPort (listPorts 0 In (map fst a @ map fst b) ! (i + length a))"
        using B(1) by (simp add: nth_append)
      show "listPorts 0 In (map fst a @ map fst b) ! (i + length a) \<in> set (listPorts 0 In (map fst a @ map fst b))"
        using B(1) by (metis add.commute add_less_mono1 length_append length_map listPorts_length nth_mem)
    qed
    moreover have
      "OpenPort (Port Out i (fst (b ! i)))
      \<in> OpenPort ` set (listPorts 0 Out (map fst b @ map fst a))"
    proof (rule image_eqI)
      show "OpenPort (Port Out i (fst (b ! i))) = OpenPort (listPorts 0 Out (map fst b @ map fst a) ! i)"
        using B(1) by (simp add: nth_append)
      show "listPorts 0 Out (map fst b @ map fst a) ! i \<in> set (listPorts 0 Out (map fst b @ map fst a))"
        using B(1) by (metis length_append length_map listPorts_length nth_mem trans_less_add1)
    qed
    ultimately show ?thesis
      by (simp del: listPorts.simps) blast
  qed
  then show "edge_from e \<in> set (pgraphPlaces ?G)" and "edge_to e \<in> set (pgraphPlaces ?G)"
    by simp_all
next
  fix m n
  assume "m \<in> set (pg_nodes ?G)"
     and "n \<in> set (pg_nodes ?G)"
     and "node_name m = node_name n"
  then show "m = n"
    by simp
next
  fix p
  assume "p \<in> set (pg_ports ?G)"
  then show "port.index p < length (filter (\<lambda>x. port.side x = (port.side p)) (pg_ports ?G))"
    by (fastforce elim: in_set_zipE simp add: split_def)
next
  fix p q
  assume "p \<in> set (pg_ports ?G)"
    and "q \<in> set (pg_ports ?G)"
    and "port.side p = port.side q"
    and "port.index p = port.index q"
  then show "port.label p = port.label q"
    by (fastforce simp add: set_zip)
next
  fix n p q
  assume "n \<in> set (pg_nodes ?G)"
     and "p \<in> set (node_ports n)"
     and "q \<in> set (node_ports n)"
     and "port.side p = port.side q"
     and "port.index p = port.index q"
  then show "port.label p = port.label q"
    by simp
next
  fix e f
  assume "e \<in> set (pg_edges ?G)"
     and "f \<in> set (pg_edges ?G)"
     and "edge_from e = edge_from f"
     and "edge_to e = edge_to f"
  then show "edge_label e = edge_label f"
    by (fastforce simp add: in_set_zip)
next
  show "distinct (pg_nodes ?G)"
    by simp
  show "distinct (pg_edges ?G)"
  proof -
    have "distinct
      (zip (map OpenPort (listPorts 0 In (map fst a)))
        (zip (map OpenPort (listPorts (length b) Out (map fst a)))
         (map snd a)))"
      by (meson distinct_listPorts distinct_map distinct_zipI1 inj_on_OpenPort)
    moreover have "distinct
      (zip (map OpenPort (listPorts (length a) In (map fst b)))
        (zip (map OpenPort (listPorts 0 Out (map fst b)))
          (map snd b)))"
      by (meson distinct_listPorts distinct_map distinct_zipI1 distinct_zipI2 inj_on_OpenPort)
    moreover have
      " set
          (zip (map OpenPort (listPorts 0 In (map fst a)))
            (zip (map OpenPort (listPorts (length b) Out (map fst a)))
              (map snd a))) \<inter>
        set
          (zip (map OpenPort (listPorts (length a) In (map fst b)))
            (zip (map OpenPort (listPorts 0 Out (map fst b)))
              (map snd b)))
      = {}"
      by safe (fastforce elim: in_set_zipE)
    ultimately show ?thesis
      by (fastforce simp add: distinct_map map3_def)
  qed
  show "distinct (pg_ports ?G)"
    by (simp del: listPorts.simps)
next
  fix e
  assume "e \<in> set (pg_edges ?G)"
     and "place_open (edge_from e)"
  then show "place_side (edge_from e) = In"
    by (fastforce elim: in_set_zipE)
next
  fix e
  assume "e \<in> set (pg_edges ?G)"
     and "place_open (edge_to e)"
  then show "place_side (edge_to e) = Out"
    by (fastforce elim: in_set_zipE)
next
  fix e
  assume "e \<in> set (pg_edges ?G)"
     and "place_ground (edge_from e)"
  then show "place_side (edge_from e) = Out"
    by (fastforce elim: in_set_zipE)
next
  fix e
  assume "e \<in> set (pg_edges ?G)"
     and "place_ground (edge_to e)"
  then show "place_side (edge_to e) = In"
    by (fastforce elim: in_set_zipE)
qed

text\<open>Swap port graph is invariant under qualification\<close>
lemma qualifyPortGraph_swapPortGraph [simp]:
  "qualifyPortGraph x (swapPortGraph a b) = swapPortGraph a b"
  by (fastforce elim: in_set_zipE simp add: qualifyPortGraph_def map3_def)

end