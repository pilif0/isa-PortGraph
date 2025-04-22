theory ForkPortGraph
  imports PortGraph
begin

section\<open>Fork Port Graph\<close>

text\<open>Fork port graph has no nodes and one input port that connects to two output ports\<close>
fun forkPortGraph :: "'a \<Rightarrow> ('s :: side_in_out, 'a, 'p, 'l) port_graph"
  where "forkPortGraph r =
  PGraph
      []
      [ Edge (OpenPort (Port In 0 r)) (OpenPort (Port Out 0 r))
      , Edge (OpenPort (Port In 0 r)) (OpenPort (Port Out 1 r))]
      [Port In 0 r, Port Out 0 r, Port Out 1 r]"

lemma port_graph_flow_forkPortGraph:
  "port_graph_flow (forkPortGraph a)" (is "port_graph_flow ?G")
proof unfold_locales
  fix e
  assume e_in: "e \<in> set (pg_edges ?G)"
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
    by simp
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

text\<open>Fork port graph is invariant under qualification\<close>
lemma qualifyPortGraph_forkPortGraph [simp]:
  "qualifyPortGraph x (forkPortGraph a) = forkPortGraph a"
  by (fastforce elim: in_set_zipE simp add: qualifyPortGraph_def)

end