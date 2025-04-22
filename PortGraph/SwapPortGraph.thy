theory SwapPortGraph
  imports PortGraph
begin

section\<open>Swap Port Graph\<close>

text\<open>
  Swap port graph has no nodes, it only connects input ports directly to output ports like identity
  but in two swapped clusters.
\<close>
fun swapPortGraph :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('s :: side_in_out, 'a, 'p, 'l) port_graph"
  where "swapPortGraph a b =
  PGraph
    []
    ( map2 Edge (map OpenPort (listPorts 0 In a))
                (map OpenPort (listPorts (length b) Out a))
    @ map2 Edge (map OpenPort (listPorts (length a) In b))
                (map OpenPort (listPorts 0 Out b)))
    (listPorts 0 In (a @ b) @ listPorts 0 Out (b @ a))"

lemma port_graph_flow_swapPortGraph:
  "port_graph_flow (swapPortGraph a b)" (is "port_graph_flow ?G")
proof unfold_locales
  fix e
  assume e_in: "e \<in> set (pg_edges ?G)"
  then consider
      "e \<in> set (map2 Edge (map OpenPort (listPorts 0 In a)) (map OpenPort (listPorts (length b) Out a)))"
    | "e \<in> set (map2 Edge (map OpenPort (listPorts (length a) In b)) (map OpenPort (listPorts 0 Out b)))"
    by fastforce
  then consider
      (A) i where "i < length a" "e = Edge (OpenPort (Port In i (a ! i))) (OpenPort (Port Out (i + length b) (a ! i)))"
    | (B) i where "i < length b" "e = Edge (OpenPort (Port In (i + length a) (b ! i))) (OpenPort (Port Out i (b ! i)))"
    by cases (fastforce elim!: in_set_map2E)+
  then have "edge_from e \<in> set (pgraphPlaces ?G) \<and> edge_to e \<in> set (pgraphPlaces ?G)"
  proof cases
    case A
    then show ?thesis
      by (simp del: listPorts.simps)
         (metis Un_iff add.commute add.right_neutral image_eqI listPorts_append listPorts_length nth_listPorts nth_mem set_append)
  next
    case B
    then show ?thesis
      by (simp del: listPorts.simps)
         (metis Un_iff add.commute add_cancel_right_left image_eqI listPorts_append listPorts_length nth_listPorts nth_mem set_append)
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
  show "distinct (pg_nodes ?G)"
    by simp
  show "distinct (pg_edges ?G)"
  proof -
    have "distinct (zip
      (map OpenPort (listPorts 0 In a))
      (map OpenPort (listPorts (length b) Out a)))"
      by (meson distinct_listPorts distinct_map distinct_zipI1 inj_on_OpenPort)
    moreover have "distinct (zip
      (map OpenPort (listPorts (length a) In b))
      (map OpenPort (listPorts 0 Out b)))"
      by (meson distinct_listPorts distinct_map distinct_zipI2 inj_on_OpenPort)
    moreover have
      " set (zip
          (map OpenPort (listPorts 0 In a))
          (map OpenPort (listPorts (length b) Out a))) \<inter>
        set (zip
          (map OpenPort (listPorts (length a) In b))
          (map OpenPort (listPorts 0 Out b)))
      = {}"
      by safe (fastforce elim: in_set_zipE)
    ultimately show ?thesis
      by (fastforce simp add: distinct_map)
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
  by (fastforce elim: in_set_zipE simp add: qualifyPortGraph_def)

end