theory NodePortGraph
  imports PortGraph
begin

section\<open>Node Port Graph\<close>

text\<open>Node port graph has one node, connecting its ports to corresponding overall ports\<close>
fun nodePortGraph :: "'p list \<Rightarrow> 'l \<Rightarrow> 'a list \<Rightarrow> 'a list  \<Rightarrow> ('s :: side_in_out, 'a, 'p, 'l) port_graph"
  where "nodePortGraph n l ins outs = PGraph
    [Node n l (listPorts 0 In ins @ listPorts 0 Out outs)]
    (map2 Edge (map OpenPort (listPorts 0 In ins))
               (map (\<lambda>p. GroundPort (QPort p n)) (listPorts 0 In ins)) @
     map2 Edge (map (\<lambda>p. GroundPort (QPort p n)) (listPorts 0 Out outs))
               (map OpenPort (listPorts 0 Out outs)))
    (listPorts 0 In ins @ listPorts 0 Out outs)"

lemma map2_append: (* TODO general theorem *)
  assumes "length xs = length ys"
  shows "map2 f xs ys @ map2 f xs' ys' = map2 f (xs @ xs') (ys @ ys')"
  using assms by simp

lemma port_graph_flow_nodePortGraph:
  "port_graph_flow (nodePortGraph n l ins outs)" (is "port_graph_flow ?G")
proof unfold_locales
  fix e
  assume "e \<in> set (pg_edges ?G)"
  then show "edge_from e \<in> set (pgraphPlaces ?G)"
        and "edge_to e \<in> set (pgraphPlaces ?G)"
    by (fastforce elim: in_set_zipE)+
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
  then show "port.index p < length (filter (\<lambda>x. port.side x = port.side p) (pg_ports ?G))"
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
    by (fastforce simp add: in_set_zip)
next
  show "distinct (pg_nodes ?G)"
    by simp
  show "distinct (pg_edges ?G)"
  proof -
    have "distinct (zip
      (map OpenPort (listPorts 0 In ins))
      (map (\<lambda>p. GroundPort (QPort p n)) (listPorts 0 In ins)))"
      by (meson distinct_listPorts distinct_map distinct_zipI1 inj_on_OpenPort)
    moreover have "distinct (zip
      (map (\<lambda>p. GroundPort (QPort p n)) (listPorts 0 Out outs))
      (map OpenPort (listPorts 0 Out outs)))"
      by (meson distinct_listPorts distinct_map distinct_zipI2 inj_on_OpenPort)
    moreover have
      " set (zip
          (map OpenPort (listPorts 0 In ins))
          (map (\<lambda>p. GroundPort (QPort p n)) (listPorts 0 In ins))) \<inter>
        set (zip
          (map (\<lambda>p. GroundPort (QPort p n)) (listPorts 0 Out outs))
          (map OpenPort (listPorts 0 Out outs)))
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

text\<open>Any node port graph edge originates in or goes to an open port\<close>
lemma nodePortGraph_edge_open:
  assumes "e \<in> set (pg_edges (nodePortGraph p l ins outs))"
  obtains "place_open (edge_from e)" | "place_open (edge_to e)"
  using assms by (fastforce elim!: in_set_zipE)

end