theory EndPortGraph
  imports PortGraph
begin

section\<open>End Port Graph\<close>

text\<open>End port graph has no nodes, edges or output ports, but it does have input ports\<close>
fun endPortGraph :: "'a list \<Rightarrow> ('s :: side_in_out, 'a, 'p, 'l) port_graph"
  where "endPortGraph a = PGraph [] [] (listPorts 0 In a)"

lemma port_graph_flow_endPortGraph:
  "port_graph_flow (endPortGraph a)" (is "port_graph_flow ?G")
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
    by simp
  show "distinct (pg_ports ?G)"
    by (simp del: listPorts.simps)
next
  fix e
  assume "e \<in> set (pg_edges ?G)"
     and "place_open (edge_from e)"
  then show "place_side (edge_from e) = In"
    by simp
next
  fix e
  assume "e \<in> set (pg_edges ?G)"
     and "place_open (edge_to e)"
  then show "place_side (edge_to e) = Out"
    by simp
next
  fix e
  assume "e \<in> set (pg_edges ?G)"
     and "place_ground (edge_from e)"
  then show "place_side (edge_from e) = Out"
    by simp
next
  fix e
  assume "e \<in> set (pg_edges ?G)"
     and "place_ground (edge_to e)"
  then show "place_side (edge_to e) = In"
    by simp
qed

text\<open>End port graph is invariant under qualification\<close>
lemma qualifyPortGraph_endPortGraph [simp]:
  "qualifyPortGraph x (endPortGraph a) = endPortGraph a"
  by (fastforce elim: in_set_zipE simp add: qualifyPortGraph_def)

end