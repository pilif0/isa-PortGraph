theory PortGraph
  imports
    Port
    PortGraph_Util
begin

section\<open>Port Graphs\<close>

subsection\<open>Types\<close>

text\<open>
  Places are what edges can connect:
  \<^item> Ground ports are inputs and outputs of nodes, so they are based on qualified ports.
  \<^item> Open ports are top-level inputs and outputs, so they are just ports (unqualified).
\<close>
datatype ('s, 'a, 'p) place =
    place_ground: GroundPort "('s, 'a, 'p) qualified_port"
  | place_open: OpenPort "('s, 'a) port"

lemma inj_on_GroundPort [simp]:
  "inj_on GroundPort A"
  by (simp add: inj_on_def)

lemma inj_on_OpenPort [simp]:
  "inj_on OpenPort A"
  by (simp add: inj_on_def)

lemma not_place_open [simp]:
  "(\<not> place_open x) = place_ground x"
  using place.exhaust_disc by blast

lemma not_place_ground:
  "(\<not> place_ground x) = place_open x"
  using place.exhaust_disc by blast

primrec (nonexhaustive) place_name :: "('s, 'a, 'p) place \<Rightarrow> 'p list"
  where "place_name (GroundPort qp) = qualified_port.name qp"

primrec place_port :: "('s, 'a, 'p) place \<Rightarrow> ('s, 'a) port"
  where
    "place_port (GroundPort qp) = qualified_port.port qp"
  | "place_port (OpenPort p) = p"

lemma un_OpenPort_place_port [simp]:
  "place_open p \<Longrightarrow> un_OpenPort p = place_port p"
  by (cases p ; simp)

fun place_side :: "('s, 'a, 'p) place \<Rightarrow> 's"
  where "place_side p = port.side (place_port p)"

text\<open>Edges are simply pairs of places\<close>
(* We could consider hyper-edges in the future *)
datatype ('s, 'a, 'p) edge = Edge (edge_from: "('s, 'a, 'p) place") (edge_to: "('s, 'a, 'p) place")

lemma inj_on_Edge [simp]:
  "inj_on (\<lambda>(x, y). Edge x y) A"
  using inj_on_def by fastforce

lemma edge_eqE:
  assumes "x = y"
  obtains "edge_from x = edge_from y"
      and "edge_to x = edge_to y"
  using assms by simp_all

text\<open>
  Nodes have:
  \<^item> Name formed from a sequence of atoms,
  \<^item> Label to carry any relevant content,
  \<^item> Ports attached to the node.
\<close>
datatype ('s, 'a, 'p, 'l) node = Node (node_name: "'p list") (node_label: 'l) (node_ports: "('s, 'a) port list")

lemma node_eqE:
  assumes "x = y"
  obtains "node_name x = node_name y"
      and "node_label x = node_label y"
      and "node_ports x = node_ports y"
  using assms by simp_all

text\<open>Port graph collects nodes, edges and (top-level) ports in lists\<close>
(*
  Lists are used as representation of finite sets to aid computation and allow mutual recursion in
  the future for hiearchical port graphs.
 *)
datatype ('s, 'a, 'p, 'l) port_graph =
  PGraph (pg_nodes: "('s, 'a, 'p, 'l) node list") (pg_edges: "('s, 'a, 'p) edge list") (pg_ports: "('s, 'a) port list")

text\<open>Two port graphs are disjoint when any pair of nodes from them have distinct names\<close>
definition pg_disjoint :: "('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> bool"
  where "pg_disjoint x y = (\<forall>m n. m \<in> set (pg_nodes x) \<and> n \<in> set (pg_nodes y) \<longrightarrow> node_name m \<noteq> node_name n)"

lemma pg_disjointI [intro!]:
  assumes "\<And>m n. \<lbrakk>m \<in> set (pg_nodes x); n \<in> set (pg_nodes y)\<rbrakk> \<Longrightarrow> node_name m \<noteq> node_name n"
  shows "pg_disjoint x y"
  using assms by (simp add: pg_disjoint_def)

lemma pg_disjoint_trivialI1:
  "pg_nodes x = [] \<Longrightarrow> pg_disjoint x y"
  by clarsimp

lemma pg_disjoint_trivialI2:
  "pg_nodes y = [] \<Longrightarrow> pg_disjoint x y"
  by clarsimp

lemma pg_disjointD:
  assumes "pg_disjoint x y"
      and "m \<in> set (pg_nodes x)"
      and "n \<in> set (pg_nodes y)"
    shows "node_name m \<noteq> node_name n"
  using assms by (simp add: pg_disjoint_def)

lemma pg_disjointE [elim]:
  assumes "pg_disjoint x y"
      and "(\<And>m n. \<lbrakk>m \<in> set (pg_nodes x); n \<in> set (pg_nodes y)\<rbrakk> \<Longrightarrow> node_name m \<noteq> node_name n) \<Longrightarrow> R"
    shows R
  using assms by (simp add: pg_disjoint_def)

lemma pg_disjoint_setD:
  assumes "pg_disjoint x y"
      and "n \<in> set (pg_nodes x)"
    shows "node_name n \<notin> node_name ` set (pg_nodes y)"
  using assms by blast

lemma sym_pg_disjoint [sym]:
  "pg_disjoint x y \<Longrightarrow> pg_disjoint y x"
  using pg_disjointD pg_disjointI by metis

text\<open>Having a node in two disjoint port graphs is a contradiction\<close>
lemma pg_disjoint_disjoint [simp]:
  assumes "pg_disjoint x y"
      and "n \<in> set (pg_nodes x)"
      and "n \<in> set (pg_nodes y)"
    shows False
  using assms pg_disjointD by metis

subsection\<open>Collecting Places\<close>

text\<open>Get the places associated with a node by qualifying its ports\<close>
fun nodePlaces :: "('s, 'a, 'p, 'l) node \<Rightarrow> ('s, 'a, 'p) place list"
  where "nodePlaces n = map (\<lambda>p. GroundPort (QPort p (node_name n))) (node_ports n)"

text\<open>One place being associated with two nodes means their names (paths) are the same\<close>
lemma nodePlaces_node_name:
  "\<lbrakk>p \<in> set (nodePlaces x); p \<in> set (nodePlaces y)\<rbrakk> \<Longrightarrow> node_name x = node_name y"
  by fastforce

text\<open>Any place associated with a node is some ground port qualified with the node's name\<close>
lemma nodePlacesE:
  assumes "x \<in> set (nodePlaces n)"
  obtains p where "x = GroundPort (QPort p (node_name n))"
  using assms by fastforce

text\<open>So no open port is associated to a node\<close>
lemma open_in_nodePlaces:
  "OpenPort x \<in> set (nodePlaces y) \<Longrightarrow> False"
  using nodePlacesE by blast

text\<open>Name of a place of some node is the name of that node\<close>
lemma nodePlaces_name [simp]:
  "p \<in> set (nodePlaces n) \<Longrightarrow> place_name p = node_name n"
  by (fastforce elim: nodePlacesE)

text\<open>Get all places in a port graph: all the nodes' places and the open ports\<close>
fun pgraphPlaces :: "('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p) place list"
  where "pgraphPlaces x = concat (map nodePlaces (pg_nodes x)) @ map OpenPort (pg_ports x)"

text\<open>Ground port in a port graph's places must be a place of some node in the graph\<close>
lemma pgraphPlaces_ground:
  assumes "p \<in> set (pgraphPlaces G)"
      and "place_ground p"
  obtains n where "n \<in> set (pg_nodes G)" and "p \<in> set (nodePlaces n)"
  using assms by fastforce

text\<open>Place in two disjoint port graphs must be an open port\<close>
lemma place_in_pg_disjoint:
  fixes x y :: "('s, 'a, 'p, 'l) port_graph"
  assumes "pg_disjoint x y"
      and "p \<in> set (pgraphPlaces x)"
      and "p \<in> set (pgraphPlaces y)"
    shows "place_open p"
  using assms by (meson pg_disjointE nodePlaces_node_name pgraphPlaces_ground place.exhaust_disc)

subsection\<open>Finding Node by Name\<close>

(* Get the element of singleton list or nothing otherwise - helper for next definition *)
fun someSingleton :: "'a list \<Rightarrow> 'a option"
  where
    "someSingleton [] = None"
  | "someSingleton [x] = Some x"
  | "someSingleton (x#y#zs) = None"

lemma someSingleton_eq_Some [simp]:
  "(someSingleton xs = Some x) = (xs = [x])"
  using someSingleton.elims by auto

lemma list_nonempty_eq_single:
  assumes "x \<in> set xs"
      and "length xs < 2"
    shows "xs = [x]"
proof -
  have "length xs \<noteq> 0"
    using assms(1) by force
  then have "length xs = 1"
    using assms(2) by presburger
  then show ?thesis
    using assms(1) by (fastforce simp add: length_Suc_conv)
qed

text\<open>Assuming node names are unique, we can use them to look up nodes\<close>
fun findNode :: "('s, 'a, 'p, 'l) port_graph \<Rightarrow> 'p list \<Rightarrow> ('s, 'a, 'p, 'l) node option"
  where "findNode G path = someSingleton (filter (\<lambda>n. node_name n = path) (pg_nodes G))"

subsection\<open>Well-Formed Port Graphs\<close>

text\<open>
  We constrain the general port graph datatype with the following assumptions:
  \<^item> All edges start and end at some place of the port graph
  \<^item> Names of nodes are unique within the port graph
  \<^item> Labels are not important for distinguishing open ports.
  \<^item> Node, edge and port lists are distinct (i.e. they nicely represent sets)
\<close>
locale port_graph =
  fixes G :: "('s, 'a, 'p, 'l) port_graph"
  assumes edge_from_pg: "\<And>e. e \<in> set (pg_edges G) \<Longrightarrow> edge_from e \<in> set (pgraphPlaces G)"
      and edge_to_pg: "\<And>e. e \<in> set (pg_edges G) \<Longrightarrow> edge_to e \<in> set (pgraphPlaces G)"
      and node_unique_path: "\<And>m n. \<lbrakk>m \<in> set (pg_nodes G); n \<in> set (pg_nodes G); node_name m = node_name n\<rbrakk> \<Longrightarrow> m = n"
      and ports_index_bound: "\<And>p. p \<in> set (pg_ports G) \<Longrightarrow> port.index p < length (filter (\<lambda>x. port.side x = port.side p) (pg_ports G))"
      and open_ports_label_eq: "\<And>p q. \<lbrakk>p \<in> set (pg_ports G); q \<in> set (pg_ports G); port.side p = port.side q; port.index p = port.index q\<rbrakk>
            \<Longrightarrow> port.label p = port.label q"
      and node_ports_label_eq: "\<And>n p q. \<lbrakk>n \<in> set (pg_nodes G); p \<in> set (node_ports n); q \<in> set (node_ports n); port.side p = port.side q; port.index p = port.index q\<rbrakk>
            \<Longrightarrow> port.label p = port.label q"
      and nodes_distinct: "distinct (pg_nodes G)"
      and edges_distinct: "distinct (pg_edges G)"
      and ports_distinct: "distinct (pg_ports G)"
begin

text\<open>In well-behaved port graphs not finding a single node means it is not present\<close>
lemma findNode_None:
  assumes "findNode G p = None"
      and "node_name x = p"
    shows "x \<notin> set (pg_nodes G)"
proof -
  consider "filter (\<lambda>n. node_name n = p) (pg_nodes G) = []"
    | a b c where "filter (\<lambda>n. node_name n = p) (pg_nodes G) = a # b # c"
    by (metis assms(1) findNode.simps not_None_eq someSingleton.elims)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using assms by (fastforce simp add: filter_empty_conv)
  next
    case 2
    have "node_name a = p"
      using 2 by (meson filter_eq_ConsD)
    moreover have "a \<in> set (pg_nodes G)"
      using 2 by (metis Cons_eq_filterD in_set_conv_decomp)
    moreover have "node_name b = p"
      using 2 by (metis (mono_tags, lifting) filter_eq_ConsD)
    moreover have "b \<in> set (pg_nodes G)"
      using 2 by (metis filter_set insert_iff list.set(2) member_filter)
    moreover have "a \<noteq> b"
      by (metis 2 distinct_filter distinct_length_2_or_more nodes_distinct)
    ultimately show ?thesis
      using node_unique_path by simp
  qed
qed

text\<open>Find the node to which a place is attached\<close>
primrec attachedTo :: "('s, 'a, 'p) place \<Rightarrow> ('s, 'a, 'p, 'l) node option"
  where
    "attachedTo (GroundPort qport) = findNode G (qualified_port.name qport)"
  | "attachedTo (OpenPort port) = None"

text\<open>
  A place attached to some node must be a ground place and that node must be found in this port
  graph under the place's name.
\<close>
lemma attachedTo_SomeE:
  assumes "attachedTo p = Some n"
  obtains "place_ground p"
      and "findNode G (place_name p) = Some n"
  using assms by (cases p ; simp)

text\<open>Name of a place attached to a node is the name of that node\<close>
lemma attachedTo_Some_name [simp]:
  assumes "attachedTo p = Some n"
  shows "place_name p = node_name n"
proof -
  have "n \<in> set (filter (\<lambda>n. node_name n = place_name p) (pg_nodes G))"
    using assms by (elim attachedTo_SomeE) simp
  then show ?thesis
    by simp
qed

text\<open>
  Any node to which a place is attached is in the port graph, because @{const attachedTo} only looks
  within this port graph.
\<close>
lemma attachedTo_pg_nodes [simp]:
  assumes "attachedTo p = Some n"
    shows "n \<in> set (pg_nodes G)"
proof -
  have "n \<in> set (filter (\<lambda>n. node_name n = place_name p) (pg_nodes G))"
    using assms by (elim attachedTo_SomeE) simp
  then show ?thesis
    by simp
qed

text\<open>If some place is a place of a node of the graph then it is attached to it in that graph.\<close>
lemma attachedToI:
  assumes "p \<in> set (nodePlaces n)"
      and "n \<in> set (pg_nodes G)"
    shows "attachedTo p = Some n"
proof -
  have n: "n \<in> set (filter (\<lambda>n. node_name n = place_name p) (pg_nodes G))"
    using assms by fastforce
  moreover have "length (filter (\<lambda>n. node_name n = place_name p) (pg_nodes G)) < 2"
  proof (rule ccontr)
    assume "\<not> length (filter (\<lambda>n. node_name n = place_name p) (pg_nodes G)) < 2"
    moreover have "distinct (filter (\<lambda>n. node_name n = place_name p) (pg_nodes G))"
      using distinct_filter nodes_distinct by blast
    ultimately obtain m
      where "m \<in> set (filter (\<lambda>n. node_name n = place_name p) (pg_nodes G))"
        and contr: "m \<noteq> n"
      using n by (metis One_nat_def Suc_1 distinct_Ex1 length_pos_if_in_set not_less_eq nth_mem)
    then have "node_name m = node_name n"
          and "m \<in> set (pg_nodes G)"
      using assms(1) by force+
    then show False
      using assms(2) node_unique_path contr by simp
  qed
  ultimately show ?thesis
    using assms(1) by (fastforce elim: nodePlacesE simp add: list_nonempty_eq_single)
qed

text\<open>If we find a node to which a place of the port graph is attached, it is in the node's places.\<close>
lemma attachedTo_nodePlaces:
  assumes "attachedTo p = Some n"
      and "p \<in> set (pgraphPlaces G)"
    shows "p \<in> set (nodePlaces n)"
proof -
  have "place_ground p"
    using assms(1) by (elim attachedTo_SomeE)
  then obtain m where p_in: "p \<in> set (nodePlaces m)" and "m \<in> set (pg_nodes G)"
    using assms(2) by (elim pgraphPlaces_ground)
  then have "attachedTo p = Some m"
    by (intro attachedToI)
  then have "m = n"
    using assms(1) by simp
  then show ?thesis
    using p_in by (rule subst)
qed

text\<open>Together with @{thm nodePlacesE} this means the place is a ground port.\<close>
lemmas attachedTo_ground = attachedTo_nodePlaces[THEN nodePlacesE]

text\<open>For any ground port of the port graph we have the node of the port graph it is attached to\<close>
lemma groundPort_attached_obtain:
  assumes "p \<in> set (pgraphPlaces G)"
      and "place_ground p"
    obtains n where "attachedTo p = Some n" and "n \<in> set (pg_nodes G)"
  using assms by (blast elim: pgraphPlaces_ground intro: attachedToI)

text\<open>The port of any open place of the graph is in ports of the graph\<close>
lemma open_port_pg:
  assumes "place_open p"
      and "p \<in> set (pgraphPlaces G)"
    shows "place_port p \<in> set (pg_ports G)"
  using assms by fastforce

end

text\<open>
  If we have one well-formed port graph and another port graph with the same node, edge and port
  lists that each have no duplicates, then the other port graph is also well-formed
\<close>
lemma port_graph_permute:
  assumes "port_graph x"
      and "set (pg_nodes x) = set (pg_nodes y)"
      and "set (pg_edges x) = set (pg_edges y)"
      and "set (pg_ports x) = set (pg_ports y)"
      and "distinct (pg_nodes y)"
      and "distinct (pg_edges y)"
      and "distinct (pg_ports y)"
    shows "port_graph y"
proof standard
  show "\<And>e. e \<in> set (pg_edges y) \<Longrightarrow> edge_from e \<in> set (pgraphPlaces y)"
    using assms port_graph.edge_from_pg by simp blast
  show "\<And>e. e \<in> set (pg_edges y) \<Longrightarrow> edge_to e \<in> set (pgraphPlaces y)"
    using assms port_graph.edge_to_pg by simp blast
  show "\<And>m n. \<lbrakk>m \<in> set (pg_nodes y); n \<in> set (pg_nodes y); node_name m = node_name n\<rbrakk> \<Longrightarrow> m = n"
    using assms port_graph.node_unique_path by blast
  show "\<And>p. p \<in> set (pg_ports y) \<Longrightarrow> port.index p < length (filter (\<lambda>x. port.side x = port.side p) (pg_ports y))"
    using assms port_graph.ports_index_bound port_graph.ports_distinct distinct_length_filter by metis
  show "\<And>p q. \<lbrakk>p \<in> set (pg_ports y); q \<in> set (pg_ports y); port.side p = port.side q;
            port.index p = port.index q\<rbrakk> \<Longrightarrow> port.label p = port.label q"
    using assms port_graph.open_ports_label_eq by blast
  show "\<And>n p q. \<lbrakk>n \<in> set (pg_nodes y); p \<in> set (node_ports n); q \<in> set (node_ports n); port.side p = port.side q;
            port.index p = port.index q\<rbrakk> \<Longrightarrow> port.label p = port.label q"
    using assms port_graph.node_ports_label_eq by blast
qed (rule assms)+

subsection\<open>Port Graphs with Flow\<close>

text\<open>Edge is ``in flow'' if it touches some input or output place\<close>
definition edge_in_flow :: "('s :: side_in_out, 'a, 'p) edge \<Rightarrow> bool"
  where "edge_in_flow e = (place_side (edge_from e) \<in> {In, Out} \<or> place_side (edge_to e) \<in> {In, Out})"

lemma edge_in_flowI:
  "place_side (edge_from e) = In \<Longrightarrow> edge_in_flow e"
  "place_side (edge_from e) = Out \<Longrightarrow> edge_in_flow e"
  "place_side (edge_to e) = In \<Longrightarrow> edge_in_flow e"
  "place_side (edge_to e) = Out \<Longrightarrow> edge_in_flow e"
  by (simp_all add: edge_in_flow_def)

lemma edge_in_flowE [elim]:
  assumes "edge_in_flow e"
      and "place_side (edge_from e) = In \<Longrightarrow> R"
      and "place_side (edge_from e) = Out \<Longrightarrow> R"
      and "place_side (edge_to e) = In \<Longrightarrow> R"
      and "place_side (edge_to e) = Out \<Longrightarrow> R"
    shows R
  using assms edge_in_flow_def by blast

text\<open>
  We further constrain port graphs in terms of how relevant edges ``flow'':
  \<^item> Edges from open ports go from open inputs
  \<^item> Edges into open ports go to open outputs
  \<^item> Edges from ground ports go from node outputs
  \<^item> Edges into ground ports go to node inputs
\<close>
(* TODO Can this flow be loosened in the presence of other sides than just In and Out? *)
locale port_graph_flow =
  port_graph G for G :: "('s :: side_in_out, 'a, 'p, 'l) port_graph" +
  assumes edge_from_open:
    "\<lbrakk>e \<in> set (pg_edges G); edge_in_flow e; place_open (edge_from e)\<rbrakk> \<Longrightarrow> place_side (edge_from e) = In"
      and edge_to_open:
    "\<lbrakk>e \<in> set (pg_edges G); edge_in_flow e; place_open (edge_to e)\<rbrakk> \<Longrightarrow> place_side (edge_to e) = Out"
      and edge_from_ground:
    "\<lbrakk>e \<in> set (pg_edges G); edge_in_flow e; place_ground (edge_from e)\<rbrakk> \<Longrightarrow> place_side (edge_from e) = Out"
      and edge_to_ground:
    "\<lbrakk>e \<in> set (pg_edges G); edge_in_flow e; place_ground (edge_to e)\<rbrakk> \<Longrightarrow> place_side (edge_to e) = In"
begin

text\<open>These assumptions give us more specific case splits for edge origins and destinations\<close>
lemma edge_from_cases [consumes 2, case_names Open Ground]:
  assumes "e \<in> set (pg_edges G)"
      and "edge_in_flow e"
  obtains
    (Open) "place_open (edge_from e)" and "place_side (edge_from e) = In"
  | (Ground) "place_ground (edge_from e)" and "place_side (edge_from e) = Out"
  using assms edge_from_ground edge_from_open not_place_ground by blast

lemma edge_to_cases [consumes 2, case_names Open Ground]:
  assumes "e \<in> set (pg_edges G)"
      and "edge_in_flow e"
  obtains
    (Open) "place_open (edge_to e)" and "place_side (edge_to e) = Out"
  | (Ground) "place_ground (edge_to e)" and "place_side (edge_to e) = In"
  using assms edge_to_ground edge_to_open not_place_ground by blast

text\<open>It follows that edge origin and destination are always distinct\<close>
lemma no_self_loop:
  assumes "e \<in> set (pg_edges G)"
      and "edge_in_flow e"
    shows "edge_from e \<noteq> edge_to e"
  using assms
  by (cases rule: edge_from_cases ; cases rule: edge_to_cases) fastforce+

end

text\<open>
  If we have one well-formed port graph with flow and another port graph with the same node, edge
  and port lists that each have no duplicates, then the other port graph is also well-formed and
  has flow.
\<close>
lemma port_graph_flow_permute:
  fixes x y :: "('s :: side_in_out, 'a, 'p, 'l) port_graph"
  assumes "port_graph_flow x"
      and "set (pg_nodes x) = set (pg_nodes y)"
      and "set (pg_edges x) = set (pg_edges y)"
      and "set (pg_ports x) = set (pg_ports y)"
      and "distinct (pg_nodes y)"
      and "distinct (pg_edges y)"
      and "distinct (pg_ports y)"
    shows "port_graph_flow y"
proof (intro port_graph_flow.intro, unfold port_graph_flow_axioms_def, safe)
  show "port_graph y"
    using assms port_graph_permute port_graph_flow.axioms(1) by metis
  show "\<And>e. \<lbrakk>e \<in> set (pg_edges y); edge_in_flow e; place_open (edge_from e)\<rbrakk> \<Longrightarrow> place_side (edge_from e) = In"
    using assms port_graph_flow.edge_from_open by metis
  show "\<And>e. \<lbrakk>e \<in> set (pg_edges y); edge_in_flow e; place_open (edge_to e)\<rbrakk> \<Longrightarrow> place_side (edge_to e) = Out"
    using assms port_graph_flow.edge_to_open by metis
  show "\<And>e. \<lbrakk>e \<in> set (pg_edges y); edge_in_flow e; place_ground (edge_from e)\<rbrakk> \<Longrightarrow> place_side (edge_from e) = Out"
    using assms port_graph_flow.edge_from_ground by metis
  show "\<And>e. \<lbrakk>e \<in> set (pg_edges y); edge_in_flow e; place_ground (edge_to e)\<rbrakk> \<Longrightarrow> place_side (edge_to e) = In"
    using assms port_graph_flow.edge_to_ground by metis
qed

subsection\<open>Renaming Port Graphs\<close>

text\<open>Nodes can be renamed with a function on paths\<close>
definition renameNode :: "('p list \<Rightarrow> 'p list) \<Rightarrow> ('s, 'a, 'p, 'l) node \<Rightarrow> ('s, 'a, 'p, 'l) node"
  where "renameNode f n = Node (f (node_name n)) (node_label n) (node_ports n)"

lemma renameNode_simps [simp]:
  "renameNode f (Node x y z) = Node (f x) y z"
  "node_name (renameNode f n) = f (node_name n)"
  "node_label (renameNode f n) = node_label n"
  "node_ports (renameNode f n) = node_ports n"
  by (simp_all add: renameNode_def)

lemma renameNode_id [simp]:
  "renameNode id = id"
  by (fastforce intro: node.expand)

lemma renameNode_comp [simp]:
  "renameNode (g \<circ> f) = renameNode g \<circ> renameNode f"
proof
  fix x :: "('a, 'b, 'c, 'd) node"
  show "renameNode (g \<circ> f) x = (renameNode g \<circ> renameNode f) x"
    by (cases x) simp_all
qed

lemma renameNode_twice [simp]:
  "renameNode g (renameNode f x) = renameNode (\<lambda>x. g (f x)) x"
  by (cases x; simp)

lemma renameNode_inj_on:
    fixes f :: "'p list \<Rightarrow> 'p list"
      and A :: "('s, 'a, 'p, 'l) node set"
  assumes "inj_on f (node_name ` A)"
    shows "inj_on (renameNode f) A"
proof
  fix x y :: "('s, 'a, 'p, 'l) node"
  assume "renameNode f x = renameNode f y"
     and "x \<in> A" and "y \<in> A"
  then show "x = y"
    using assms
    by simp (metis (mono_tags, lifting) image_eqI inj_on_contraD node.expand renameNode_simps(2,3,4))
qed

lemma renameNode_inj:
  "inj f \<Longrightarrow> inj (renameNode f)"
  using renameNode_inj_on by (metis inj_on_subset top_greatest)

lemma renameNode_inv:
  "bij f \<Longrightarrow> renameNode (inv f) = inv (renameNode f)"
  by (fastforce intro: node.expand inv_equality[symmetric] injI elim: node_eqE simp add: bij_def surj_iff_all)

text\<open>Places can be renamed with a function on paths\<close>
primrec renamePlace :: "('p list \<Rightarrow> 'p list) \<Rightarrow> ('s, 'a, 'p) place \<Rightarrow> ('s, 'a, 'p) place"
  where
    "renamePlace f (GroundPort qport) = GroundPort (renameQPort f qport)"
  | "renamePlace f (OpenPort port) = OpenPort port"

lemma renamePlace_simps [simp]:
  "place_ground p \<Longrightarrow> place_name (renamePlace f p) = f (place_name p)"
  "place_open p \<Longrightarrow> renamePlace f p = p"
  "place_ground (renamePlace f p) = place_ground p"
  "place_open (renamePlace f p) = place_open p"
  "place_port (renamePlace f p) = place_port p"
  by (cases p ; simp)+

lemma renamePlace_id [simp]:
  "renamePlace id = id"
proof
  fix x :: "('x, 'y, 'z) place"
  show "renamePlace id x = id x"
    by (cases x ; simp)
qed

text\<open>Define a way to gather all names in a set of places\<close>
definition namesOfPlaces :: "('s, 'a, 'p) place set \<Rightarrow> 'p list set"
  where "namesOfPlaces A = {n. \<exists>p \<in> A. place_ground p \<and> place_name p = n}"

lemma namesOfPlaces_Un:
  "namesOfPlaces (A \<union> B) = namesOfPlaces A \<union> namesOfPlaces B"
  by (simp add: namesOfPlaces_def) blast

lemma renamePlace_inj_on:
    fixes f :: "'p list \<Rightarrow> 'p list"
      and A :: "('s, 'a, 'p) place set"
  assumes "inj_on f (namesOfPlaces A)"
    shows "inj_on (renamePlace f) A"
proof
  fix x y :: "('s, 'a, 'p) place"
  assume f_eq: "renamePlace f x = renamePlace f y"
     and x: "x \<in> A" and y: "y \<in> A"

  consider
    (Ground) xQP yQP where "x = GroundPort xQP" and "y = GroundPort yQP"
  | (Open) xP yP where "x = OpenPort xP" and "y = OpenPort yP"
    using f_eq by (metis place.exhaust_sel renamePlace.simps(1,2))
  then show "x = y"
  proof cases
    case Ground

    have "qualified_port.name xQP \<in> {n. \<exists>p\<in>A. place_ground p \<and> place_name p = n}"
      using x Ground(1) by force
    moreover have "qualified_port.name yQP \<in> {n. \<exists>p\<in>A. place_ground p \<and> place_name p = n}"
      using y Ground(2) by force
    moreover have "f (qualified_port.name xQP) = f (qualified_port.name yQP)"
      using f_eq Ground by (metis place.disc(1) place_name.simps renamePlace_simps(1))
    ultimately have "qualified_port.name xQP = qualified_port.name yQP"
      using assms inj_on_eq_iff by (metis (mono_tags, lifting) namesOfPlaces_def)
    moreover have "qualified_port.port xQP = qualified_port.port yQP"
      using f_eq Ground by (metis place_port.simps(1) renamePlace_simps(5))
    ultimately have "xQP = yQP"
      using qualified_port.expand by metis
    then show ?thesis
      using Ground by simp
  next
    case Open
    then show ?thesis using f_eq by simp
  qed
qed

lemma renamePlace_inj:
  "inj f \<Longrightarrow> inj (renamePlace f)"
  using renamePlace_inj_on by (metis inj_on_subset top_greatest)

lemma renamePlace_inv [simp]:
  fixes f :: "'p list \<Rightarrow> 'p list"
  assumes "bij f"
  shows "renamePlace (inv f) = inv (renamePlace f)"
proof (intro inv_equality[symmetric])
  fix x :: "('x, 'y, 'p) place"
  show "renamePlace (inv f) (renamePlace f x) = x"
    using assms by (cases x ; simp add: bij_is_inj renameQPort_inj)
  show "renamePlace f (renamePlace (inv f) x) = x"
  proof (cases x)
    case (GroundPort qp)
    then show ?thesis
      using assms by simp (metis (no_types, lifting) bij_betw_imp_inj_on bij_betw_imp_surj_on inv_f_eq renameQPort_inj renameQPort_inv surj_imp_inj_inv)
  next
    case (OpenPort p)
    then show ?thesis
      using assms by simp
  qed
qed

lemma renamePlace_comp [simp]:
  "renamePlace (g \<circ> f) = renamePlace g \<circ> renamePlace f"
proof
  fix x :: "('a, 'b, 'c) place"
  show "renamePlace (g \<circ> f) x = (renamePlace g \<circ> renamePlace f) x"
    by (cases x) simp_all
qed

lemma renamePlace_twice [simp]:
  "renamePlace g (renamePlace f x) = renamePlace (\<lambda>x. g (f x)) x"
  by (cases x; simp)

text\<open>Edges can be renamed with a function on paths\<close>
definition renameEdge :: "('p list \<Rightarrow> 'p list) \<Rightarrow> ('s, 'a, 'p) edge \<Rightarrow> ('s, 'a, 'p) edge"
  where "renameEdge f e = Edge (renamePlace f (edge_from e)) (renamePlace f (edge_to e))"

lemma renameEdge_simps [simp]:
  "renameEdge f (Edge from to) = Edge (renamePlace f from) (renamePlace f to)"
  "edge_from (renameEdge f e) = renamePlace f (edge_from e)"
  "edge_to (renameEdge f e) = renamePlace f (edge_to e)"
  by (simp_all add: renameEdge_def)

lemma renameEdge_id [simp]:
  "renameEdge id = id"
  by (fastforce intro: edge.expand)

lemma renameEdge_in_flow [simp]:
  "edge_in_flow (renameEdge f e) = edge_in_flow e"
  by (simp add: edge_in_flow_def)

lemma renameEdge_inj_on:
    fixes f :: "'p list \<Rightarrow> 'p list"
      and A :: "('s, 'a, 'p) edge set"
  assumes "inj_on f (namesOfPlaces (edge_from ` A) \<union> namesOfPlaces (edge_to ` A))"
    shows "inj_on (renameEdge f) A"
proof
  fix x y :: "('s, 'a, 'p) edge"
  assume "renameEdge f x = renameEdge f y"
     and "x \<in> A" and "y \<in> A"
  then show "x = y"
    by (cases x, cases y, simp)
       (metis (mono_tags, lifting) assms edge.sel(1,2) image_eqI inj_on_Un inj_on_eq_iff renamePlace_inj_on)
qed

lemma renameEdge_inj:
  "inj f \<Longrightarrow> inj (renameEdge f)"
  using renameEdge_inj_on by (metis inj_on_subset top_greatest)

lemma renameEdge_inv [simp]:
  fixes f :: "'p list \<Rightarrow> 'p list"
  assumes "bij f"
  shows "renameEdge (inv f) = inv (renameEdge f)"
proof (intro inv_equality[symmetric])
  fix x :: "('x, 'y, 'p) edge"
  show "renameEdge (inv f) (renameEdge f x) = x"
    using assms by (simp add: renameEdge_def bij_is_inj renamePlace_inj)
  show "renameEdge f (renameEdge (inv f) x) = x"
    using assms
    by (simp add: renameEdge_def) (metis (full_types) bij_betw_def edge.exhaust_sel inv_f_f renamePlace_inj renamePlace_inv surj_imp_inj_inv)
qed

lemma renameEdge_comp [simp]:
  "renameEdge (g \<circ> f) = renameEdge g \<circ> renameEdge f"
proof
  fix x :: "('a, 'b, 'c) edge"
  show "renameEdge (g \<circ> f) x = (renameEdge g \<circ> renameEdge f) x"
    by (cases x) simp_all
qed

lemma renameEdge_twice [simp]:
  "renameEdge g (renameEdge f x) = renameEdge (\<lambda>x. g (f x)) x"
  by (cases x; simp)

text\<open>
  For well-formed port graphs, an invertible renaming on its places induces an invertible renaming
  on its edges
\<close>
lemma (in port_graph) inv_on_edges:
  assumes "\<And>p. p \<in> set (pgraphPlaces G) \<Longrightarrow> renamePlace g (renamePlace f p) = p"
      and "e \<in> set (pg_edges G)"
    shows "renameEdge g (renameEdge f e) = e"
  by (metis (no_types, lifting) assms edge.expand renameEdge_simps(2,3) edge_from_pg edge_to_pg)

subsection\<open>Qualifying Port Graphs\<close>

text\<open>Nodes can be qualified with a path element\<close>
definition qualifyNode :: "'p \<Rightarrow> ('s, 'a, 'p, 'l) node \<Rightarrow> ('s, 'a, 'p, 'l) node"
  where "qualifyNode x n = Node (x # node_name n) (node_label n) (node_ports n)"

lemma qualifyNode_simps [simp]:
  "qualifyNode a (Node x y z) = Node (a # x) y z"
  "node_name (qualifyNode a n) = a # (node_name n)"
  "node_label (qualifyNode a n) = node_label n"
  "node_ports (qualifyNode a n) = node_ports n"
  by (simp_all add: qualifyNode_def)

lemma qualifyNode_rename:
  "qualifyNode x = renameNode ((#) x)"
  by standard (simp add: qualifyNode_def renameNode_def)

definition unqualifyNode :: "nat \<Rightarrow> ('s, 'a, 'p, 'l) node \<Rightarrow> ('s, 'a, 'p, 'l) node"
  where "unqualifyNode n x = Node (drop n (node_name x)) (node_label x) (node_ports x)"

lemma unqualifyNode_simps [simp]:
  "unqualifyNode a (Node x y z) = Node (drop a x) y z"
  "node_name (unqualifyNode a n) = drop a (node_name n)"
  "node_label (unqualifyNode a n) = node_label n"
  "node_ports (unqualifyNode a n) = node_ports n"
  by (simp_all add: unqualifyNode_def)

lemma unqualifyNode_rename:
  "unqualifyNode x = renameNode (drop x)"
  by standard (simp add: unqualifyNode_def renameNode_def)

lemma unqualify_qualify_node_inv [simp]:
  "unqualifyNode 1 (qualifyNode n x) = x"
  by (simp add: unqualifyNode_def)

lemma inj_qualifyNode:
  "inj (qualifyNode a)"
  by (meson inj_on_inverseI unqualify_qualify_node_inv)

text\<open>Qualifying nodes is injective on their paths\<close>
lemma qualifyNode_name_inj:
  assumes "node_name (qualifyNode a x) = node_name (qualifyNode a y)"
  shows "node_name x = node_name y"
  using assms by simp

text\<open>Places can be qualified with a path element\<close>
primrec qualifyPlace :: "'p \<Rightarrow> ('s, 'a, 'p) place \<Rightarrow> ('s, 'a, 'p) place"
  where
    "qualifyPlace x (GroundPort qport) = GroundPort (qualifyQPort x qport)"
  | "qualifyPlace x (OpenPort port) = OpenPort port"

lemma qualifyPlace_simps [simp]:
  "place_ground p \<Longrightarrow> place_name (qualifyPlace a p) = a # (place_name p)"
  "place_open p \<Longrightarrow> qualifyPlace a p = p"
  "place_ground (qualifyPlace a p) = place_ground p"
  "place_open (qualifyPlace a p) = place_open p"
  "place_port (qualifyPlace a p) = place_port p"
  by (cases p ; simp)+

lemma qualifyPlace_rename:
  fixes x :: 'p
  shows "qualifyPlace x = renamePlace ((#) x)"
proof
  fix p :: "('x, 'y, 'p) place"
  show "qualifyPlace x p = renamePlace ((#) x) p"
    by (cases p ; simp add: qualifyQPort_rename)
qed

primrec unqualifyPlace :: "nat \<Rightarrow> ('s, 'a, 'p) place \<Rightarrow> ('s, 'a, 'p) place"
  where
    "unqualifyPlace n (GroundPort qport) = GroundPort (unqualifyQPort n qport)"
  | "unqualifyPlace n (OpenPort port) = OpenPort port"

lemma unqualifyPlace_simps [simp]:
  "place_ground p \<Longrightarrow> place_name (unqualifyPlace a p) = drop a (place_name p)"
  "place_open p \<Longrightarrow> unqualifyPlace a p = p"
  "place_ground (unqualifyPlace a p) = place_ground p"
  "place_open (unqualifyPlace a p) = place_open p"
  "place_port (unqualifyPlace a p) = place_port p"
  by (cases p ; simp)+

lemma unqualifyPlace_rename:
  "unqualifyPlace x = renamePlace (drop x)"
proof
  fix p :: "('x, 'y, 'z) place"
  show "unqualifyPlace x p = renamePlace (drop x) p"
    by (cases p ; simp add: unqualifyQPort_rename)
qed

lemma unqualify_qualify_place_inv [simp]:
  "unqualifyPlace 1 (qualifyPlace n x) = x"
  by (metis place.exhaust qualifyPlace.simps unqualifyPlace.simps unqualify_qualify_qport_inv)

lemma inj_qualifyPlace:
  "inj (qualifyPlace a)"
  by (meson inj_on_inverseI unqualify_qualify_place_inv)

text\<open>Qualifying an open port does not change it, so it does not change a list of them\<close>
lemma map_qualify_open_port [simp]:
  "map (qualifyPlace x) (map OpenPort xs) = map OpenPort xs"
  by simp

text\<open>
  Qualifying ground ports just after constructing them with no path can be merged with the
  construction
\<close>
lemma map_qualify_ground_port:
  "map (qualifyPlace x) (map (\<lambda>p. GroundPort (QPort p [])) xs) = map (\<lambda>p. GroundPort (QPort p [x])) xs"
  by simp

text\<open>Places of qualified node are qualified places of original node\<close>
lemma qualifyNode_places:
  "nodePlaces (qualifyNode a x) = map (qualifyPlace a) (nodePlaces x)"
  by simp

text\<open>Edges can be qualified with a path element\<close>
definition qualifyEdge :: "'p \<Rightarrow> ('s, 'a, 'p) edge \<Rightarrow> ('s, 'a, 'p) edge"
  where "qualifyEdge x e = Edge (qualifyPlace x (edge_from e)) (qualifyPlace x (edge_to e))"

lemma qualifyEdge_simps [simp]:
  "qualifyEdge x (Edge from to) = Edge (qualifyPlace x from) (qualifyPlace x to)"
  "edge_from (qualifyEdge a e) = qualifyPlace a (edge_from e)"
  "edge_to (qualifyEdge a e) = qualifyPlace a (edge_to e)"
  by (simp_all add: qualifyEdge_def)

lemma qualifyEdge_rename:
  "qualifyEdge x = renameEdge ((#) x)"
  by standard (simp add: qualifyEdge_def qualifyPlace_rename renameEdge_def)

lemma qualifyEdge_in_flow [simp]:
  "edge_in_flow (qualifyEdge x e) = edge_in_flow e"
  by (simp add: edge_in_flow_def)

definition unqualifyEdge :: "nat \<Rightarrow> ('s, 'a, 'p) edge \<Rightarrow> ('s, 'a, 'p) edge"
  where "unqualifyEdge n e = Edge (unqualifyPlace n (edge_from e)) (unqualifyPlace n (edge_to e))"

lemma unqualifyEdge_simps [simp]:
  "unqualifyEdge n (Edge from to) = Edge (unqualifyPlace n from) (unqualifyPlace n to)"
  "edge_from (unqualifyEdge a e) = unqualifyPlace a (edge_from e)"
  "edge_to (unqualifyEdge a e) = unqualifyPlace a (edge_to e)"
  by (simp_all add: unqualifyEdge_def)

lemma unqualifyEdge_rename:
  "unqualifyEdge x = renameEdge (drop x)"
  by standard (simp add: unqualifyEdge_def unqualifyPlace_rename renameEdge_def)

lemma unqualify_qualify_edge_inv [simp]:
  "unqualifyEdge 1 (qualifyEdge n x) = x"
  by (simp add: unqualifyEdge_def del: One_nat_def)

lemma inj_qualifyEdge:
  "inj (qualifyEdge a)"
  by (meson inj_on_inverseI unqualify_qualify_edge_inv)

text\<open>Qualifying edges just after constructing them can be merged with the construction\<close>
lemma qualify_map2_edge [simp]:
  assumes "length xs = length ys"
  shows "map (qualifyEdge p) (map2 Edge xs ys) = map2 Edge (map (qualifyPlace p) xs) (map (qualifyPlace p) ys)"
  using assms by (simp add: split_def zip_map_map)

text\<open>Port graphs can be qualified with a path element\<close>
definition qualifyPortGraph :: "'p \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) port_graph"
  where "qualifyPortGraph x g = PGraph (map (qualifyNode x) (pg_nodes g)) (map (qualifyEdge x) (pg_edges g)) (pg_ports g)"

lemma qualifyPortGraph_simps [simp]:
  "qualifyPortGraph x (PGraph nodes edges ports) = PGraph (map (qualifyNode x) nodes) (map (qualifyEdge x) edges) ports"
  "pg_nodes (qualifyPortGraph a x) = map (qualifyNode a) (pg_nodes x)"
  "pg_edges (qualifyPortGraph a x) = map (qualifyEdge a) (pg_edges x)"
  "pg_ports (qualifyPortGraph a x) = pg_ports x"
  by (simp_all add: qualifyPortGraph_def)

definition unqualifyPortGraph :: "nat \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) port_graph"
  where "unqualifyPortGraph n g = PGraph (map (unqualifyNode n) (pg_nodes g)) (map (unqualifyEdge n) (pg_edges g)) (pg_ports g)"

lemma unqualifyPortGraph_simps [simp]:
  "unqualifyPortGraph n (PGraph nodes edges ports) = PGraph (map (unqualifyNode n) nodes) (map (unqualifyEdge n) edges) ports"
  "pg_nodes (unqualifyPortGraph a x) = map (unqualifyNode a) (pg_nodes x)"
  "pg_edges (unqualifyPortGraph a x) = map (unqualifyEdge a) (pg_edges x)"
  "pg_ports (unqualifyPortGraph a x) = pg_ports x"
  by (simp_all add: unqualifyPortGraph_def)

lemma unqualify_qualify_pgraph_inv [simp]:
  "unqualifyPortGraph 1 (qualifyPortGraph n x) = x"
  by (simp add: unqualifyPortGraph_def comp_def del: One_nat_def)

lemma inj_qualifyPortGraph:
  "inj (qualifyPortGraph a)"
  by (meson inj_on_inverseI unqualify_qualify_pgraph_inv)

lemma pgraphPlaces_qualifyPortGraph [simp]:
  "pgraphPlaces (qualifyPortGraph a x) = map (qualifyPlace a) (pgraphPlaces x)"
  by (simp add: comp_def map_concat)

text\<open>Qualifying a well-formed port graph keeps it well-formed\<close>
lemma port_graph_qualifyPortGraph:
  fixes x :: "('s, 'a, 'b, 'c) port_graph"
  assumes "port_graph x"
    shows "port_graph (qualifyPortGraph a x)"
proof -
  interpret x: port_graph x
    using assms by simp

  show ?thesis
  proof (unfold_locales)
    fix e
    assume e: "e \<in> set (pg_edges (qualifyPortGraph a x))"

    show "edge_from e \<in> set (pgraphPlaces (qualifyPortGraph a x))"
      using e x.edge_from_pg by fastforce
    show "edge_to e \<in> set (pgraphPlaces (qualifyPortGraph a x))"
      using e x.edge_to_pg by fastforce
  next
    fix m n :: "('s, 'a, 'b, 'c) node"
    assume "m \<in> set (pg_nodes (qualifyPortGraph a x))"
       and "n \<in> set (pg_nodes (qualifyPortGraph a x))"
       and "node_name m = node_name n"
    then show "m = n"
      using x.node_unique_path qualifyNode_simps(1) by clarsimp blast
  next
    fix p
    assume "p \<in> set (pg_ports (qualifyPortGraph a x))"
    then show "port.index p < length (filter (\<lambda>x. port.side x = port.side p) (pg_ports (qualifyPortGraph a x)))"
      using x.ports_index_bound by simp
  next
    fix p q
    assume "p \<in> set (pg_ports (qualifyPortGraph a x))"
       and "q \<in> set (pg_ports (qualifyPortGraph a x))"
       and "port.side p = port.side q"
       and "port.index p = port.index q"
    then show "port.label p = port.label q"
      using x.open_ports_label_eq by (metis qualifyPortGraph_simps(4))
  next
    fix n p q
    assume "n \<in> set (pg_nodes (qualifyPortGraph a x))"
       and "p \<in> set (node_ports n)"
       and "q \<in> set (node_ports n)"
       and "port.side p = port.side q"
       and "port.index p = port.index q"
    then show "port.label p = port.label q"
      by clarsimp (blast intro: x.node_ports_label_eq)
  next
    show "distinct (pg_nodes (qualifyPortGraph a x))"
      using x.nodes_distinct inj_qualifyNode
      by (fastforce intro: inj_on_subset simp add: distinct_map)

    show "distinct (pg_edges (qualifyPortGraph a x))"
      using x.edges_distinct inj_qualifyEdge
      by (fastforce intro: inj_on_subset simp add: distinct_map)

    show "distinct (pg_ports (qualifyPortGraph a x))"
      using x.ports_distinct by simp
  qed
qed

text\<open>Furthermore, qualifying a well-formed port graph with flow also keeps its flow\<close>
lemma port_graph_flow_qualifyPortGraph:
  fixes x :: "('s :: side_in_out, 'a, 'b, 'c) port_graph"
  assumes "port_graph_flow x"
    shows "port_graph_flow (qualifyPortGraph a x)"
proof (cases x)
  case x: (PGraph x1 x2 x3)

  interpret x: port_graph_flow x
    using assms by simp

  have "port_graph_flow_axioms (qualifyPortGraph a x)"
  proof
    fix e
    assume "e \<in> set (pg_edges (qualifyPortGraph a x))"
       and "place_open (edge_from e)"
       and "edge_in_flow e"
    then show "place_side (edge_from e) = In"
      using x.edge_from_open by clarsimp
  next
    fix e
    assume "e \<in> set (pg_edges (qualifyPortGraph a x))"
       and "place_open (edge_to e)"
       and "edge_in_flow e"
    then show "place_side (edge_to e) = Out"
      using x.edge_to_open by clarsimp
  next
    fix e
    assume "e \<in> set (pg_edges (qualifyPortGraph a x))"
       and "place_ground (edge_from e)"
       and "edge_in_flow e"
    then show "place_side (edge_from e) = Out"
      using x.edge_from_ground by clarsimp
  next
    fix e
    assume "e \<in> set (pg_edges (qualifyPortGraph a x))"
       and "place_ground (edge_to e)"
       and "edge_in_flow e"
    then show "place_side (edge_to e) = In"
      using x.edge_to_ground by clarsimp
  qed
  then show ?thesis
    using x.port_graph_axioms
    by (simp add: port_graph_flow.intro port_graph_qualifyPortGraph)
qed

text\<open>Using distinct names qualifies two port graphs apart\<close>
lemma qualifyPortGraph_apart:
  assumes "a \<noteq> b"
    shows "pg_disjoint (qualifyPortGraph a x) (qualifyPortGraph b y)"
  using assms by clarsimp

lemma pg_disjoint_qualifyPortGraph:
  "pg_disjoint (qualifyPortGraph a x) (qualifyPortGraph a y) = pg_disjoint x y"
  by fastforce

subsection\<open>Port Graph Surgeries\<close>

subsubsection\<open>Disconnecting Edges from Places\<close>

text\<open>Remove from a list of edges those that connect (from either side) to one of given places\<close>
definition disconnectFromPlaces :: "('s, 'a, 'p) place list \<Rightarrow> ('s, 'a, 'p) edge list \<Rightarrow> ('s, 'a, 'p) edge list"
  where "disconnectFromPlaces places edges = filter (\<lambda>e. edge_from e \<notin> set places \<and> edge_to e \<notin> set places) edges"

text\<open>Disconnecting from appended list is disconnecting from each sublist in sequence\<close>
lemma disconnectFromPlaces_append1:
  "disconnectFromPlaces (ps @ qs) xs = disconnectFromPlaces ps (disconnectFromPlaces qs xs)"
  by (induct xs ; simp add: disconnectFromPlaces_def edge.case_eq_if)

text\<open>Disconnecting from one list of places an appended list of edges is appended disconnecting of the sublists\<close>
lemma disconnectFromPlaces_append2:
  "disconnectFromPlaces xs (as @ bs) = disconnectFromPlaces xs as @ disconnectFromPlaces xs bs"
  by (simp add: disconnectFromPlaces_def)

text\<open>Disconnecting nothing is simply nothing\<close>
lemma disconnectFromPlaces_Nil [simp]:
  "disconnectFromPlaces ps [] = []"
  by (simp add: disconnectFromPlaces_def)

text\<open>Disconnecting multiple times in sequence can be done in any order\<close>
lemma disconnectFromPlaces_commute:
  "disconnectFromPlaces ps (disconnectFromPlaces qs es) = disconnectFromPlaces qs (disconnectFromPlaces ps es)"
  by (simp add: disconnectFromPlaces_def) meson

text\<open>Disconnecting from places used in creation of edges yields the empty list\<close>
lemma disconnectFromPlaces_map2_edge_those:
  assumes "length xs = length ys"
    shows "disconnectFromPlaces xs (map2 Edge xs ys) = []" (is ?th1)
      and "disconnectFromPlaces ys (map2 Edge xs ys) = []" (is ?th2)
proof -
  show ?th1
    using assms
  proof (induct xs arbitrary: ys)
    case Nil
    then show ?case by (simp add: disconnectFromPlaces_def)
  next
    case (Cons a as)
    then obtain b bs where ys: "ys = b # bs"
      by (metis Suc_length_conv)
    then have "disconnectFromPlaces as (map2 Edge as bs) = []"
      using Cons by fastforce
    then show ?case
      by (fastforce simp add: ys disconnectFromPlaces_def filter_empty_conv)
  qed
  show ?th2
    using assms
  proof (induct xs arbitrary: ys)
    case Nil
    then show ?case by (simp add: disconnectFromPlaces_def)
  next
    case (Cons a as)
    then obtain b bs where ys: "ys = b # bs"
      by (metis Suc_length_conv)
    then have "disconnectFromPlaces bs (map2 Edge as bs) = []"
      using Cons by fastforce
    then show ?case
      by (fastforce simp add: ys disconnectFromPlaces_def filter_empty_conv)
  qed
qed

text\<open>Disconnected edge must have been in the original list and not touched the given places\<close>
lemma disconnectFromPlaces_in_setE:
  assumes "x \<in> set (disconnectFromPlaces ps es)"
  obtains "x \<in> set es" and "edge_from x \<notin> set ps" and "edge_to x \<notin> set ps"
  using assms that by (induct es ; simp add: disconnectFromPlaces_def edge.case_eq_if)

text\<open>Filtering commutes through disconnecting edges from places\<close>
lemma disconnectFromPlaces_filter_commute:
  "disconnectFromPlaces ps (filter P es) = filter P (disconnectFromPlaces ps es)"
  by (simp add: disconnectFromPlaces_def conj_commute)

text\<open>Disconnecting from places a list of edges constructed from different places does not change it\<close>
lemma disconnectFromPlaces_neither:
  assumes "\<And>x. x \<in> set as \<Longrightarrow> x \<notin> set xs"
      and "\<And>x. x \<in> set bs \<Longrightarrow> x \<notin> set xs"
      and "length as = length bs"
    shows "disconnectFromPlaces xs (map2 Edge as bs) = map2 Edge as bs"
  using assms
  by (simp add: disconnectFromPlaces_def filter_map comp_def)
     (smt (verit, best) case_prod_unfold edge.sel(1) edge.sel(2) edge.split_sel filter_True in_set_zip le_boolD nth_mem order.refl)

text\<open>Renaming disconnected edges is the same as disconnecting renamed original edges from analogously renamed places.\<close>
lemma renameEdge_disconnectFromPlaces:
  assumes "inj_on f (namesOfPlaces (set ps) \<union> namesOfPlaces (edge_from ` set es) \<union> namesOfPlaces (edge_to ` set es))"
    shows "map (renameEdge f) (disconnectFromPlaces ps es) = disconnectFromPlaces (map (renamePlace f) ps) (map (renameEdge f) es)"
  using assms
proof (induct es)
  case Nil
  then show ?case by (simp add: disconnectFromPlaces_def)
next
  case (Cons e es)
  moreover have "inj_on f (namesOfPlaces (set ps) \<union> namesOfPlaces (edge_from ` set es) \<union> namesOfPlaces (edge_to ` set es))"
  proof -
    have "namesOfPlaces (set ps) \<subseteq> namesOfPlaces (set ps)"
      by simp
    moreover have "namesOfPlaces (edge_from ` set es) \<subseteq> namesOfPlaces (edge_from ` set (e # es))"
      by (metis image_mono le_iff_sup namesOfPlaces_Un set_subset_Cons)
    moreover have "namesOfPlaces (edge_to ` set es) \<subseteq> namesOfPlaces (edge_to ` set (e # es))"
      by (metis image_mono le_iff_sup namesOfPlaces_Un set_subset_Cons)
    ultimately have
      " namesOfPlaces (set ps) \<union> namesOfPlaces (edge_from ` set es) \<union>
        namesOfPlaces (edge_to ` set es)
      \<subseteq> namesOfPlaces (set ps) \<union> namesOfPlaces (edge_from ` set (e # es)) \<union>
        namesOfPlaces (edge_to ` set (e # es))"
      by blast
    then show ?thesis
      using Cons(2) inj_on_subset by blast
  qed
  moreover have "inj_on f (namesOfPlaces (set ps \<union> edge_from ` set (e # es)))"
    using Cons(2) namesOfPlaces_Un inj_on_Un by metis
  then have "(renamePlace f (edge_from e) \<in> renamePlace f ` set ps) = (edge_from e \<in> set ps)"
    by (metis image_subset_iff inj_on_image_mem_iff list.set_intros(1) renamePlace_inj_on sup_ge1 sup_ge2)
  moreover have "inj_on f (namesOfPlaces (set ps \<union> edge_to ` set (e # es)))"
    using Cons(2) namesOfPlaces_Un
    by (metis Un_Int_eq(1) boolean_algebra.disj_conj_distrib2 inj_on_Int)
  then have "renamePlace f (edge_to e) \<in> renamePlace f ` set ps \<equiv> edge_to e \<in> set ps"
    by (smt (verit, best) image_subset_iff inj_on_image_mem_iff list.set_intros(1) renamePlace_inj_on sup_ge1 sup_ge2)
  ultimately show ?case
    by (simp add: disconnectFromPlaces_def)
qed

text\<open>Qualifying disconnected edges is the same as disconnecting qualified original edges from analogously qualified places.\<close>
lemma qualifyEdge_disconnectFromPlaces:
  "map (qualifyEdge a) (disconnectFromPlaces ps es) = disconnectFromPlaces (map (qualifyPlace a) ps) (map (qualifyEdge a) es)"
  using renameEdge_disconnectFromPlaces qualifyEdge_rename qualifyPlace_rename by (metis inj_on_Cons1)

text\<open>If the places are all open ports, the order of renaming and disconnecting edges from them does not matter.\<close>
lemma renameEdge_disconnectFromPlaces_open:
  assumes "\<And>p. p \<in> set ps \<Longrightarrow> place_open p"
  shows "map (renameEdge f) (disconnectFromPlaces ps es) = disconnectFromPlaces ps (map (renameEdge f) es)"
proof (induct es)
  case Nil
  then show ?case by (simp add: disconnectFromPlaces_def)
next
  case (Cons a es)
  then show ?case using assms by (fastforce simp add: disconnectFromPlaces_def)
qed

subsubsection\<open>Selecting Outgoing Edges\<close>

text\<open>Predicate that is true only for edges going to open output ports\<close>
definition toOpenOut :: "('s :: side_in_out, 'a, 'p) edge \<Rightarrow> bool"
  where "toOpenOut e = (place_open (edge_to e) \<and> place_side (edge_to e) = Out)"

lemma toOpenOutE [elim!]:
  assumes "toOpenOut e"
  obtains "place_open (edge_to e)" and "place_side (edge_to e) = Out"
  using assms by (simp add: toOpenOut_def)

lemma toOpenOutI [intro!]:
  assumes "place_open (edge_to e)"
      and "place_side (edge_to e) = Out"
    shows "toOpenOut e"
  using assms by (simp add: toOpenOut_def)

text\<open>Filtering open output edges after constructing them to go to open output ports keeps all of them\<close>
lemma filter_toOpenOut_map2Edge_outs:
  assumes "length xs = length ys"
    shows " filter toOpenOut (map2 Edge xs (map OpenPort (listPorts n Out ys))) =
            map2 Edge xs (map OpenPort (listPorts n Out ys))"
proof -
  have "filter toOpenOut (map2 Edge xs ps) = map2 Edge xs ps"
    if "\<And>p. p \<in> set ps \<Longrightarrow> place_open p \<and> port.side (place_port p) = Out" and "length xs = length ps"
    for ps
    using that
  proof (induct xs arbitrary: ps)
    case Nil
    then show ?case by simp
  next
    case (Cons a as)
    then obtain b bs where "ps = b # bs" and "place_open b" and "port.side (place_port b) = Out"
      by (metis length_0_conv list.exhaust list.set_intros(1))
    then show ?case
      using Cons by (simp add: toOpenOut_def)
  qed
  then show ?thesis
    by (rule ; fastforce simp add: assms)
qed

text\<open>Filtering open output edges after constructing them to go to open input ports keeps none of them\<close>
lemma filter_toOpenOut_map2Edge_ins:
  assumes "length xs = length ys"
    shows "filter toOpenOut (map2 Edge xs (map OpenPort (listPorts n In ys))) = []"
proof -
  have "filter toOpenOut (map2 Edge xs ps) = []"
    if "\<And>p. p \<in> set ps \<Longrightarrow> place_open p \<and> port.side (place_port p) = In" and "length xs = length ps"
    for ps
    using that
  proof (induct xs arbitrary: ps)
    case Nil
    then show ?case by simp
  next
    case (Cons a as)
    then obtain b bs where "ps = b # bs" and "place_open b" and "port.side (place_port b) = In"
      by (metis length_0_conv list.exhaust list.set_intros(1))
    then show ?case
      using Cons by (simp add: toOpenOut_def)
  qed
  then show ?thesis
    by (rule ; fastforce simp add: assms)
qed

text\<open>Filtering open output edges after constructing them to go to ground ports keeps none of them\<close>
lemma filter_toOpenOut_map2Edge_ground:
  assumes "length xs = length ys"
    shows "filter toOpenOut (map2 Edge xs (map (\<lambda>p. GroundPort (f p)) ys)) = []"
proof -
  have "filter toOpenOut (map2 Edge xs ps) = []"
    if "\<And>p. p \<in> set ps \<Longrightarrow> place_ground p" and "length xs = length ps"
    for ps
    using that
  proof (induct xs arbitrary: ps)
    case Nil
    then show ?case by simp
  next
    case (Cons a as)
    then obtain b bs where "ps = b # bs" and "place_ground b"
      by (metis length_0_conv list.exhaust list.set_intros(1))
    then show ?case
      using Cons by (simp add: toOpenOut_def)
  qed
  then show ?thesis
    by (rule ; fastforce simp add: assms)
qed

lemmas filter_toOpenOut_simps [simp] =
  filter_toOpenOut_map2Edge_outs
  filter_toOpenOut_map2Edge_ins
  filter_toOpenOut_map2Edge_ground

text\<open>Filtering open output edges commutes with renaming (and qualifying) them\<close>
lemma toOpenOut_renameEdge [simp]:
  "toOpenOut (renameEdge a e) = toOpenOut e"
  by (simp add: toOpenOut_def)

lemma toOpenOut_qualifyEdge [simp]:
  "toOpenOut (qualifyEdge a e) = toOpenOut e"
  by (simp add: qualifyEdge_rename)

lemma filter_toOpenOut_renameEdge:
  "filter toOpenOut (map (renameEdge a) xs) = map (renameEdge a) (filter toOpenOut xs)"
  by (induct xs ; simp add: not_place_ground)

lemma filter_not_toOpenOut_renameEdge:
  "filter (\<lambda>x. \<not> toOpenOut x) (map (renameEdge a) xs) = map (renameEdge a) (filter (\<lambda>x. \<not> toOpenOut x) xs)"
  by (induct xs ; simp add: not_place_ground)

lemma filter_toOpenOut_qualifyEdge:
  "filter toOpenOut (map (qualifyEdge a) xs) = map (qualifyEdge a) (filter toOpenOut xs)"
  by (metis qualifyEdge_rename filter_toOpenOut_renameEdge)

lemma filter_not_toOpenOut_qualifyEdge:
  "filter (\<lambda>x. \<not> toOpenOut x) (map (qualifyEdge a) xs) = map (qualifyEdge a) (filter (\<lambda>x. \<not> toOpenOut x) xs)"
  by (metis qualifyEdge_rename filter_not_toOpenOut_renameEdge)

text\<open>
  In port graphs with flow the disconnecting from open outputs can be simplified to filtering out
  outgoing edges.
\<close>
lemma (in port_graph_flow) disconnect_out:
  " disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = Out) (pg_ports G))) (pg_edges G) =
    filter (\<lambda>x. \<not> toOpenOut x) (pg_edges G)"
proof -
  have
   "( edge_from e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = Out} \<and>
      edge_to e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = Out}) =
    (\<not> toOpenOut e)" if "e \<in> set (pg_edges G)" and "edge_in_flow e" for e
    using that
  proof (cases e rule: edge_to_cases)
    case Open
    then show ?thesis
      using that edge_to_pg by fastforce
  next
    case Ground
    moreover have "edge_from e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = Out}"
      using that by (cases e rule: edge_from_cases ; clarsimp)
    ultimately show ?thesis
      by fastforce
  qed
  moreover have
   "( edge_from e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = Out} \<and>
      edge_to e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = Out}) =
    (\<not> toOpenOut e)" if "e \<in> set (pg_edges G)" and "\<not> edge_in_flow e" for e
    using that edge_in_flow_def by fastforce
  ultimately have
   "( edge_from e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = Out} \<and>
      edge_to e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = Out}) =
    (\<not> toOpenOut e)" if "e \<in> set (pg_edges G)" for e
    using that by (cases "edge_in_flow e") blast+
  then show ?thesis
    unfolding disconnectFromPlaces_def
    by (clarsimp intro!: filter_cong[OF refl])
qed

subsubsection\<open>Selecting Incoming Edges\<close>

text\<open>Predicate that is true only for edges going from open input ports\<close>
definition fromOpenIn :: "('s :: side_in_out, 'a, 'p) edge \<Rightarrow> bool"
  where "fromOpenIn e = (place_open (edge_from e) \<and> place_side (edge_from e) = In)"

lemma fromOpenInE [elim!]:
  assumes "fromOpenIn e"
  obtains "place_open (edge_from e)" and "place_side (edge_from e) = In"
  using assms by (simp add: fromOpenIn_def)

lemma fromOpenInI [intro!]:
  assumes "place_open (edge_from e)"
      and "place_side (edge_from e) = In"
    shows "fromOpenIn e"
  using assms by (simp add: fromOpenIn_def)

text\<open>Filtering open input edges after constructing them to go from open input ports keeps all of them\<close>
lemma filter_fromOpenIn_map2Edge_ins:
  assumes "length xs = length ys"
    shows " filter fromOpenIn (map2 Edge (map OpenPort (listPorts n In xs)) ys) =
            map2 Edge (map OpenPort (listPorts n In xs)) ys"
proof -
  have "filter fromOpenIn (map2 Edge ps ys) = map2 Edge ps ys"
    if "\<And>p. p \<in> set ps \<Longrightarrow> place_open p \<and> port.side (place_port p) = In" and "length ys = length ps"
    for ps
    using that
  proof (induct ys arbitrary: ps)
    case Nil
    then show ?case by simp
  next
    case (Cons a as)
    then obtain b bs where "ps = b # bs" and "place_open b" and "port.side (place_port b) = In"
      by (metis length_0_conv list.exhaust list.set_intros(1))
    then show ?case
      using Cons by (simp add: fromOpenIn_def)
  qed
  then show ?thesis
    by (rule ; fastforce simp add: assms)
qed

text\<open>Filtering open input edges after constructing them to go from open output ports keeps none of them\<close>
lemma filter_fromOpenIn_map2Edge_outs:
  assumes "length xs = length ys"
    shows "filter fromOpenIn (map2 Edge (map OpenPort (listPorts n Out xs)) ys) = []"
proof -
  have "filter fromOpenIn (map2 Edge ps ys) = []"
    if "\<And>p. p \<in> set ps \<Longrightarrow> place_open p \<and> port.side (place_port p) = Out" and "length ys = length ps"
    for ps
    using that
  proof (induct ys arbitrary: ps)
    case Nil
    then show ?case by simp
  next
    case (Cons a as)
    then obtain b bs where "ps = b # bs" and "place_open b" and "port.side (place_port b) = Out"
      by (metis length_0_conv list.exhaust list.set_intros(1))
    then show ?case
      using Cons by (simp add: fromOpenIn_def)
  qed
  then show ?thesis
    by (rule ; fastforce simp add: assms)
qed

text\<open>Filtering open input edges after constructing them to go from ground ports keeps none of them\<close>
lemma filter_fromOpenIn_map2Edge_ground:
  assumes "length xs = length ys"
    shows "filter fromOpenIn (map2 Edge (map (\<lambda>p. GroundPort (f p)) xs) ys) = []"
proof -
  have "filter fromOpenIn (map2 Edge ps ys) = []"
    if "\<And>p. p \<in> set ps \<Longrightarrow> place_ground p" and "length ys = length ps"
    for ps
    using that
  proof (induct ys arbitrary: ps)
    case Nil
    then show ?case by simp
  next
    case (Cons a as)
    then obtain b bs where "ps = b # bs" and "place_ground b"
      by (metis length_0_conv list.exhaust list.set_intros(1))
    then show ?case
      using Cons by (simp add: fromOpenIn_def)
  qed
  then show ?thesis
    by (rule ; fastforce simp add: assms)
qed

lemmas filter_fromOpenIn_simps [simp] =
  filter_fromOpenIn_map2Edge_outs
  filter_fromOpenIn_map2Edge_ins
  filter_fromOpenIn_map2Edge_ground

text\<open>Filtering open input edges commutes with renaming (and qualifying) them\<close>
lemma fromOpenIn_renameEdge [simp]:
  "fromOpenIn (renameEdge a e) = fromOpenIn e"
  by (simp add: fromOpenIn_def)

lemma fromOpenIn_qualifyEdge [simp]:
  "fromOpenIn (qualifyEdge a e) = fromOpenIn e"
  by (simp add: qualifyEdge_rename)

lemma filter_fromOpenIn_renameEdge:
  "filter fromOpenIn (map (renameEdge a) xs) = map (renameEdge a) (filter fromOpenIn xs)"
  by (induct xs ; simp add: not_place_ground)

lemma filter_not_fromOpenIn_renameEdge:
  "filter (\<lambda>x. \<not> fromOpenIn x) (map (renameEdge a) xs) = map (renameEdge a) (filter (\<lambda>x. \<not> fromOpenIn x)  xs)"
  by (induct xs ; simp add: not_place_ground)

lemma filter_fromOpenIn_qualifyEdge:
  "filter fromOpenIn (map (qualifyEdge a) xs) = map (qualifyEdge a) (filter fromOpenIn xs)"
  by (metis qualifyEdge_rename filter_fromOpenIn_renameEdge)

lemma filter_not_fromOpenIn_qualifyEdge:
  "filter (\<lambda>x. \<not> fromOpenIn x) (map (qualifyEdge a) xs) = map (qualifyEdge a) (filter (\<lambda>x. \<not> fromOpenIn x) xs)"
  by (metis qualifyEdge_rename filter_not_fromOpenIn_renameEdge)

text\<open>
  In port graphs with flow the disconnecting from open inputs can be simplified to filtering out
  incoming edges.
\<close>
lemma (in port_graph_flow) disconnect_in:
  " disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = In) (pg_ports G))) (pg_edges G) =
    filter (\<lambda>x. \<not> fromOpenIn x) (pg_edges G)"
proof -
  have
   "( edge_from e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = In} \<and>
      edge_to e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = In}) =
    (\<not> fromOpenIn e)" if "e \<in> set (pg_edges G)" and "edge_in_flow e" for e
    using that
  proof (cases e rule: edge_from_cases)
    case Open
    then show ?thesis
      using that edge_from_pg by fastforce
  next
    case Ground
    moreover have "edge_to e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = In}"
      using that by (cases e rule: edge_to_cases ; clarsimp)
    ultimately show ?thesis
      using that by fastforce
  qed
  moreover have
   "( edge_from e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = In} \<and>
      edge_to e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = In}) =
    (\<not> fromOpenIn e)" if "e \<in> set (pg_edges G)" and "\<not> edge_in_flow e" for e
    using that edge_in_flow_def by fastforce
  ultimately have
   "( edge_from e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = In} \<and>
      edge_to e \<notin> OpenPort ` {p \<in> set (pg_ports G). port.side p = In}) =
    (\<not> fromOpenIn e)" if "e \<in> set (pg_edges G)" for e
    using that by (cases "edge_in_flow e") blast+
  then show ?thesis
    unfolding disconnectFromPlaces_def
    by (clarsimp intro!: filter_cong[OF refl])
qed

subsubsection\<open>Shifting Open Ports\<close>

text\<open>Port index can be shifted up by some natural number which may depend on its side\<close>
(* Side dependence is used to not have to enumerate all sides in juxtaposition *)
definition shiftPort :: "('s \<Rightarrow> nat) \<Rightarrow> ('s, 'a) port \<Rightarrow> ('s, 'a) port"
  where "shiftPort n p = Port (port.side p) (n (port.side p) + port.index p) (port.label p)"

lemma shiftPort_0 [simp]:
  "shiftPort (\<lambda>s. 0) = (\<lambda>x. x)"
  by standard (simp add: shiftPort_def)

lemma shiftPort_simps [simp]:
  "shiftPort n (Port s i l) = Port s (n s + i) l"
  "port.side (shiftPort n p) = port.side p"
  "port.index (shiftPort n p) = n (port.side p) + port.index p"
  "port.label (shiftPort n p) = port.label p"
  by (simp_all add: shiftPort_def)

lemma shiftPort_known:
  "port.side p = s \<Longrightarrow> shiftPort n p = shiftPort (\<lambda>x. n s) p"
  by (simp add: shiftPort_def)

lemma inj_shiftPort:
  "inj (shiftPort n)"
  by (clarsimp simp add: inj_def shiftPort_def port.expand)

text\<open>Shifting ports built from a list of labels is the same as shifting the initial index\<close>
lemma shiftPort_listPorts [simp]:
  "map (shiftPort n) (listPorts m s xs) = listPorts (n s + m) s xs"
proof -
  have "map (shiftPort n) (listPorts m s xs) = map2 (\<lambda>x. Port s (n s + x)) [m..<m + length xs] xs"
    by fastforce
  also have "... = map2 (Port s) (map ((+) (n s)) [m..<m + length xs]) xs"
    by (simp add: map_zip_map)
  also have "... = map2 (Port s) [n s + m..<n s + m + length xs] xs"
  proof -
    { fix x y
      have "map ((+) (n s)) [x..< y] = [n s + x ..< n s + y]"
        by (induct "y - x" arbitrary: x y ; simp add: upt_conv_Cons)
    }
    then show ?thesis
      by (simp add: add.assoc)
  qed
  finally show ?thesis
    by simp
qed

text\<open>Filtering ports by side commutes with shifting their indices\<close>
lemma filter_port_side_shiftPort:
  "filter (\<lambda>x. port.side x = s) (map (shiftPort n) ps) = map (shiftPort n) (filter (\<lambda>x. port.side x = s) ps)"
  by (induct ps ; simp)

text\<open>Shifting a port twice shifts it by the added amount\<close>
lemma shiftPort_twice [simp]:
  "shiftPort m (shiftPort n x) = shiftPort (\<lambda>s. m s + n s) x"
  by (simp add: port.expand)

lemma map_shiftPort_twice [simp]:
  "map (shiftPort m) (map (shiftPort n) xs) = map (shiftPort (\<lambda>s. m s + n s)) xs"
  by (induct xs ; simp)

text\<open>We can selectively shift ports in open places by an amount that may depend on its side\<close>
primrec shiftOpenPlace :: "('s \<Rightarrow> nat) \<Rightarrow> ('s, 'a, 'p) place \<Rightarrow> ('s, 'a, 'p) place"
  where
    "shiftOpenPlace n (GroundPort p) = GroundPort p"
  | "shiftOpenPlace n (OpenPort p) = OpenPort (shiftPort n p)"

lemma shiftOpenPlace_0 [simp]:
  "shiftOpenPlace (\<lambda>s. 0) = (\<lambda>x. x)"
proof
  fix x :: "('x, 'y, 'z) place"
  show "shiftOpenPlace (\<lambda>s. 0) x = x"
    by (case_tac x ; simp)
qed

lemma shiftOpenPlace_known:
  "(place_open p \<Longrightarrow> place_side p = s) \<Longrightarrow> shiftOpenPlace n p = shiftOpenPlace (\<lambda>x. n s) p"
  by (cases p) (simp_all, rule shiftPort_known)

lemma shiftOpenPlace_ground [simp]:
  "place_ground (shiftOpenPlace n p) = place_ground p"
  "place_ground p \<Longrightarrow> shiftOpenPlace n p = p"
  by (cases p ; simp)+

lemma shiftOpenPlace_open [simp]:
  "place_open (shiftOpenPlace n p) = place_open p"
  "place_open p \<Longrightarrow> place_port (shiftOpenPlace n p) = shiftPort n (place_port p)"
  by (cases p ; simp)+

lemma shiftOpenPlace_side [simp]:
  "place_side (shiftOpenPlace n p) = place_side p"
  by (cases p) simp_all

lemma shiftOpenPlace_label [simp]:
  "port.label (place_port (shiftOpenPlace n p)) = port.label (place_port p)"
  by (cases p) simp_all

lemma inj_shiftOpenPlace:
  "inj (shiftOpenPlace n)"
proof
  fix x y :: "('a, 'y, 'z) place"
  assume a: "shiftOpenPlace n x = shiftOpenPlace n y"
  then show "x = y"
    using inj_shiftPort by (cases x ; cases y ; fastforce simp add: inj_def shiftPort_def)
qed

text\<open>Shifting open places built from a list of labels is the same as shifting the initial index\<close>
lemma shiftOpenPlace_listPorts [simp]:
  " map (shiftOpenPlace n) (map OpenPort (listPorts m s xs)) =
    map OpenPort (listPorts (n s + m) s xs)"
proof -
  have "map (shiftOpenPlace n) (map OpenPort (listPorts m s xs)) =
        map OpenPort (map (shiftPort n) (listPorts m s xs))"
    by fastforce
  then show ?thesis
    by (simp only: shiftPort_listPorts)
qed

text\<open>Shifting an open place twice shifts it by the added amount\<close>
lemma shiftOpenPlace_twice [simp]:
  "shiftOpenPlace m (shiftOpenPlace n x) = shiftOpenPlace (\<lambda>s. m s + n s) x"
  by (cases x ; simp)

lemma map_shiftOpenPlace_twice [simp]:
  "map (shiftOpenPlace m) (map (shiftOpenPlace n) xs) = map (shiftOpenPlace (\<lambda>s. m s + n s)) xs"
  by (induct xs ; simp)

text\<open>Qualifying an open place after possibly shifting it is shifting the qualified place\<close>
lemma renamePlace_shiftOpenPlace [simp]:
  "renamePlace f (shiftOpenPlace n x) = shiftOpenPlace n (renamePlace f x)"
  by (cases x ; simp)

lemma qualifyPlace_shiftOpenPlace [simp]:
  "qualifyPlace a (shiftOpenPlace n x) = shiftOpenPlace n (qualifyPlace a x)"
  by (simp add: qualifyPlace_rename)

text\<open>We can apply open place shift on both ends of an edge, by amounts that may depend on the place's side\<close>
definition shiftOpenInEdge :: "('s \<Rightarrow> nat) \<Rightarrow> ('s \<Rightarrow> nat) \<Rightarrow> ('s, 'a, 'p) edge \<Rightarrow> ('s, 'a, 'p) edge"
  where "shiftOpenInEdge m n e = Edge (shiftOpenPlace m (edge_from e)) (shiftOpenPlace n (edge_to e))"

lemma shiftOpenInEdge_0_0 [simp]:
  "shiftOpenInEdge (\<lambda>s. 0) (\<lambda>s. 0) = (\<lambda>x. x)"
  by standard (simp add: shiftOpenInEdge_def)

lemma shiftOpenInEdge_simps [simp]:
  "edge_from (shiftOpenInEdge m n e) = shiftOpenPlace m (edge_from e)"
  "edge_to (shiftOpenInEdge m n e) = shiftOpenPlace n (edge_to e)"
  by (simp_all add: shiftOpenInEdge_def)

lemma shiftOpenInEdge_known:
  "(place_open (edge_from e) \<Longrightarrow> place_side (edge_from e) = s) \<Longrightarrow> shiftOpenInEdge m n e = shiftOpenInEdge (\<lambda>x. m s) n e"
  "(place_open (edge_to e) \<Longrightarrow> place_side (edge_to e) = s) \<Longrightarrow> shiftOpenInEdge m n e = shiftOpenInEdge m (\<lambda>x. n s) e"
  by (simp_all add: shiftOpenInEdge_def)
     (metis place_side.simps shiftOpenPlace_known)+

lemma inj_shiftOpenInEdge:
  "inj (shiftOpenInEdge m n)"
  by standard (simp add: inj_eq edge.expand inj_shiftOpenPlace shiftOpenInEdge_def)

text\<open>
  Shifting a list of edges just after constructing them can be decomposed into shifting the open
  places from which they are being constructed
\<close>
lemma map_shiftOpenInEdge_map2:
  " map (shiftOpenInEdge m n) (map2 Edge xs ys) =
    map2 Edge (map (shiftOpenPlace m) xs) (map (shiftOpenPlace n) ys)"
  by (clarsimp simp add: comp_def map2_map_each shiftOpenInEdge_def)

text\<open>Shifting an edge twice shifts it by the added amount\<close>
lemma shiftOpenInEdge_twice [simp]:
  "shiftOpenInEdge m n (shiftOpenInEdge m' n' x) = shiftOpenInEdge (\<lambda>s. m s + m' s) (\<lambda>s. n s + n' s) x"
  by (simp add: shiftOpenInEdge_def)

lemma map_shiftOpenInEdge_twice [simp]:
  "map (shiftOpenInEdge m n) (map (shiftOpenInEdge m' n') xs) = map (shiftOpenInEdge (\<lambda>s. m s + m' s) (\<lambda>s. n s + n' s)) xs"
  by (induct xs ; simp)

text\<open>Qualifying an edge after possibly shifting it is shifting the qualified edge\<close>
lemma renameEdge_shiftOpenInEdge [simp]:
  "renameEdge f (shiftOpenInEdge m n x) = shiftOpenInEdge m n (renameEdge f x)"
  by (simp add: shiftOpenInEdge_def)

lemma map_renameEdge_shiftOpenInEdge:
  "map (renameEdge f) (map (shiftOpenInEdge m n) xs) = map (shiftOpenInEdge m n) (map (renameEdge f) xs)"
  by (induct xs ; simp)

lemma image_renameEdge_shiftOpenInEdge:
  "renameEdge f ` shiftOpenInEdge m n ` A = shiftOpenInEdge m n ` renameEdge f ` A"
  by (metis (mono_tags, lifting) comp_apply image_comp image_cong renameEdge_shiftOpenInEdge)

lemma qualifyEdge_shiftOpenInEdge [simp]:
  "qualifyEdge a (shiftOpenInEdge m n x) = shiftOpenInEdge m n (qualifyEdge a x)"
  by (simp add: qualifyEdge_rename)

lemma map_qualifyEdge_shiftOpenInEdge:
  "map (qualifyEdge a) (map (shiftOpenInEdge m n) xs) = map (shiftOpenInEdge m n) (map (qualifyEdge a) xs)"
  by (induct xs ; simp)

text\<open>Shifting edges commutes with filtering out open input or output edges\<close>
lemma shiftOpenInEdge_toOpenOut [simp]:
  "toOpenOut (shiftOpenInEdge a b x) = toOpenOut x"
  by (cases "edge_to x" ; simp add: toOpenOut_def)

lemma map_shiftOpenInEdge_filter_toOpenOut:
  "map (shiftOpenInEdge a b) (filter toOpenOut xs) = filter toOpenOut (map (shiftOpenInEdge a b) xs)"
  by (induct xs ; simp)

lemma map_shiftOpenInEdge_filter_not_toOpenOut:
  "map (shiftOpenInEdge a b) (filter (\<lambda>x. \<not> toOpenOut x) xs) = filter (\<lambda>x. \<not> toOpenOut x) (map (shiftOpenInEdge a b) xs)"
  by (induct xs ; simp)

lemma shiftOpenInEdge_fromOpenIn [simp]:
  "fromOpenIn (shiftOpenInEdge a b x) = fromOpenIn x"
  by (cases "edge_from x" ; simp add: fromOpenIn_def)

lemma map_shiftOpenInEdge_filter_fromOpenIn:
  "map (shiftOpenInEdge a b) (filter fromOpenIn xs) = filter fromOpenIn (map (shiftOpenInEdge a b) xs)"
  by (induct xs ; simp)

lemma map_shiftOpenInEdge_filter_not_fromOpenIn:
  "map (shiftOpenInEdge a b) (filter (\<lambda>x. \<not> fromOpenIn x) xs) = filter (\<lambda>x. \<not> fromOpenIn x) (map (shiftOpenInEdge a b) xs)"
  by (induct xs ; simp)

text\<open>Shifting an edge changes the indices to at least the shift amount\<close>
lemma
  assumes "e = shiftOpenInEdge m n x"
    shows shiftOpenInEdge_from_index_bound: "place_open (edge_from e) \<Longrightarrow> port.index (place_port (edge_from e)) \<ge> m (place_side (edge_from e))"
      and shiftOpenInEdge_to_index_bound: "place_open (edge_to e) \<Longrightarrow> port.index (place_port (edge_to e)) \<ge> n (place_side (edge_to e))"
  by (simp_all add: assms)

text\<open>Shifting open ports in an edge does not change whether it is in the flow\<close>
lemma shiftOpenInEdge_in_flow [simp]:
  "edge_in_flow (shiftOpenInEdge f g e) = edge_in_flow e"
  by (simp add: shiftOpenInEdge_def edge_in_flow_def del: place_side.simps)

subsection\<open>Port Graph Equivalence\<close>

text\<open>
  Two port graphs are equivalent if they are both ill formed, or if they are both well-formed, have
  the same open ports and there exists two functions on their paths such that:
  \<^item> Renaming nodes of @{term x} with @{term f} gives the nodes of @{term y};
  \<^item> Renaming nodes of @{term y} with @{term g} gives the nodes of @{term x};
  \<^item> And the same for renaming edges.
\<close>
(* Predicate for witnessing functions is split out to help reuse steps in proofs *)
(* TODO better document it *)
definition pgEquiv_witness :: "('p list \<Rightarrow> 'p list) \<Rightarrow> ('p list \<Rightarrow> 'p list) \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> bool"
  where "pgEquiv_witness f g x y \<equiv>
    renameNode f ` (set (pg_nodes x)) = set (pg_nodes y) \<and>
    set (pg_nodes x) = renameNode g ` (set (pg_nodes y)) \<and>
    renameEdge f ` (set (pg_edges x)) = set (pg_edges y) \<and>
    set (pg_edges x) = renameEdge g ` (set (pg_edges y)) \<and>
    (\<forall>l. l \<in> node_name ` set (pg_nodes x) \<longrightarrow> g (f l) = l) \<and>
    (\<forall>l. l \<in> node_name ` set (pg_nodes y) \<longrightarrow> f (g l) = l)"

lemma pgEquiv_witnessI [intro]:
  assumes "renameNode f ` (set (pg_nodes x)) = set (pg_nodes y)"
      and "set (pg_nodes x) = renameNode g ` (set (pg_nodes y))"
      and "renameEdge f ` (set (pg_edges x)) = set (pg_edges y)"
      and "set (pg_edges x) = renameEdge g ` (set (pg_edges y))"
      and "\<And>l. l \<in> node_name ` set (pg_nodes x) \<Longrightarrow> g (f l) = l"
      and "\<And>l. l \<in> node_name ` set (pg_nodes y) \<Longrightarrow> f (g l) = l"
    shows "pgEquiv_witness f g x y"
  unfolding pgEquiv_witness_def
  using assms by blast

lemma pgEquiv_witnessE [elim]:
  assumes "pgEquiv_witness f g x y"
  obtains "renameNode f ` (set (pg_nodes x)) = set (pg_nodes y)"
      and "set (pg_nodes x) = renameNode g ` (set (pg_nodes y))"
      and "renameEdge f ` (set (pg_edges x)) = set (pg_edges y)"
      and "set (pg_edges x) = renameEdge g ` (set (pg_edges y))"
      and "\<And>l. l \<in> node_name ` set (pg_nodes x) \<Longrightarrow> g (f l) = l"
      and "\<And>l. l \<in> node_name ` set (pg_nodes y) \<Longrightarrow> f (g l) = l"
  using assms
  unfolding pgEquiv_witness_def
  by metis

lemma pgEquiv_witness_id [simp]:
  "pgEquiv_witness id id x y = (set (pg_nodes x) = set (pg_nodes y) \<and> set (pg_edges x) = set (pg_edges y))"
  by (simp add: pgEquiv_witness_def)

lemma pgEquiv_witness_sym:
  "pgEquiv_witness f g x y \<Longrightarrow> pgEquiv_witness g f y x"
  by (simp add: pgEquiv_witness_def) metis

lemma pgEquiv_witness_trans:
  assumes "pgEquiv_witness f g x y"
      and "pgEquiv_witness h i y z"
    shows "pgEquiv_witness (h \<circ> f) (g \<circ> i) x z"
proof
  show "renameNode (h \<circ> f) ` set (pg_nodes x) = set (pg_nodes z)"
  using assms by (elim pgEquiv_witnessE) (metis renameNode_comp image_comp)
  show "set (pg_nodes x) = renameNode (g \<circ> i) ` set (pg_nodes z)"
  using assms by (elim pgEquiv_witnessE) (metis renameNode_comp image_comp)
  show "renameEdge (h \<circ> f) ` set (pg_edges x) = set (pg_edges z)"
  using assms by (elim pgEquiv_witnessE) (metis renameEdge_comp image_comp)
  show "set (pg_edges x) = renameEdge (g \<circ> i) ` set (pg_edges z)"
    using assms by (elim pgEquiv_witnessE) (metis renameEdge_comp image_comp)

  (* Mark pgEquiv_witnessE as safe for just the following two goals *)
  note [rule del] = pgEquiv_witnessE
  note [elim!] = pgEquiv_witnessE

  show "\<And>l. l \<in> node_name ` set (pg_nodes x) \<Longrightarrow> (g \<circ> i) ((h \<circ> f) l) = l"
  using assms by clarsimp (metis image_eqI renameNode_simps(2))
  show "\<And>l. l \<in> node_name ` set (pg_nodes z) \<Longrightarrow> (h \<circ> f) ((g \<circ> i) l) = l"
  using assms by clarsimp (metis image_eqI renameNode_simps(2))
qed

lemma pgEquiv_witness_bij_betw:
  assumes "pgEquiv_witness f g x y"
  shows "bij_betw f (node_name ` set (pg_nodes x)) (node_name ` set (pg_nodes y))"
    and "bij_betw g (node_name ` set (pg_nodes y)) (node_name ` set (pg_nodes x))"
proof -
  show "bij_betw f (node_name ` set (pg_nodes x)) (node_name ` set (pg_nodes y))"
    unfolding bij_betw_def inj_on_def
  proof
    show "\<forall>xa\<in>node_name ` set (pg_nodes x). \<forall>y\<in>node_name ` set (pg_nodes x). f xa = f y \<longrightarrow> xa = y"
      using assms by (metis pgEquiv_witnessE)
    show "f ` node_name ` set (pg_nodes x) = node_name ` set (pg_nodes y)"
      using assms[THEN pgEquiv_witnessE]
      by safe (metis (no_types, lifting) imageI renameNode_simps(2))+
  qed
  show "bij_betw g (node_name ` set (pg_nodes y)) (node_name ` set (pg_nodes x))"
    unfolding bij_betw_def inj_on_def
  proof
    show "\<forall>x\<in>node_name ` set (pg_nodes y). \<forall>y\<in>node_name ` set (pg_nodes y). g x = g y \<longrightarrow> x = y"
      using assms by (metis pgEquiv_witnessE)
    show "g ` node_name ` set (pg_nodes y) = node_name ` set (pg_nodes x)"
      using assms[THEN pgEquiv_witnessE]
      by safe (metis (no_types, lifting) imageI renameNode_simps(2))+
  qed
qed

definition pgEquiv :: "('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> bool" (infix "\<approx>" 50)
  where "pgEquiv x y = ((\<not> port_graph x \<and> \<not> port_graph y) \<or>
  ( port_graph x \<and>
    port_graph y \<and>
    set (pg_ports x) = set (pg_ports y) \<and>
    (\<exists>f g :: 'p list \<Rightarrow> 'p list.
      pgEquiv_witness f g x y
  )))"

lemma pgEquivI [intro]:
  assumes "port_graph x"
      and "port_graph y"
      and "set (pg_ports x) = set (pg_ports y)"
      and "pgEquiv_witness f g x y"
    shows "x \<approx> y"
  unfolding pgEquiv_def
  using assms by blast

lemma pgEquivI_ex:
  assumes "port_graph x"
      and "port_graph y"
      and "set (pg_ports x) = set (pg_ports y)"
      and "\<exists>f g. pgEquiv_witness f g x y"
    shows "x \<approx> y"
  using assms by (simp add: pgEquiv_def)

lemma pgEquivI':
  assumes "\<not> port_graph x"
      and "\<not> port_graph y"
    shows "x \<approx> y"
  using pgEquiv_def assms by blast

lemma pgEquivE [elim]:
  assumes "x \<approx> y"
  obtains f g
    where "port_graph x"
      and "port_graph y"
      and "set (pg_ports x) = set (pg_ports y)"
      and "pgEquiv_witness f g x y"
  | "\<not> port_graph x" and "\<not> port_graph y"
  using assms
  unfolding pgEquiv_def
  by metis

lemma pgEquiv_refl [simp]:
  "x \<approx> x"
proof (cases "port_graph x")
  case True
  moreover have "pgEquiv_witness id id x x"
    by simp
  ultimately show ?thesis
    using pgEquivI by blast
next
  case False
  then show ?thesis using pgEquivI' by blast
qed

lemma pgEquiv_sym [sym]:
  assumes "x \<approx> y"
  shows "y \<approx> x"
proof (cases "port_graph x")
  case pg_x: True
  then have pg_y: "port_graph y"
    using assms by blast

  show ?thesis
    using assms pgEquivE pgEquivI pgEquiv_witness_sym pg_x pg_y by metis
next
  case False
  then show ?thesis
    using assms by (meson pgEquivE pgEquivI')
qed

lemma pgEquiv_trans [trans]:
  assumes "x \<approx> y" and "y \<approx> z" shows "x \<approx> z"
proof (cases "port_graph x")
  case pg_x: True
  then have pg_y: "port_graph y"
    using assms by blast
  then have pg_z: "port_graph z"
    using assms by blast

  obtain f g
    where "pgEquiv_witness f g x y"
      and "set (pg_ports x) = set (pg_ports y)"
    using assms pgEquivE pg_x by auto
  moreover obtain f' g'
    where "pgEquiv_witness f' g' y z"
      and "set (pg_ports y) = set (pg_ports z)"
    using assms pgEquivE pg_y by auto
  ultimately show ?thesis
    using pg_x pg_z pgEquiv_witness_trans by blast
next
  case False
  then show ?thesis using assms pgEquiv_def by blast
qed

lemma pgEquiv_equivp [simp]:
  "equivp pgEquiv"
  by (simp add: equivpI pgEquiv_sym pgEquiv_trans reflpI sympI transpI)

text\<open>Qualifying a port graph produces an equivalent one\<close>
lemma pgEquiv_qualifyPortGraph:
  assumes "port_graph x"
  shows "qualifyPortGraph a x \<approx> x"
proof
  obtain n e p where x: "x = PGraph n e p"
    using port_graph.exhaust by blast

  show "port_graph (qualifyPortGraph a x)"
    using assms port_graph_qualifyPortGraph by metis
  show "port_graph x"
    by (rule assms)
  show "set (pg_ports (qualifyPortGraph a x)) = set (pg_ports x)"
    by (simp add: x)
  show "pgEquiv_witness (drop 1) ((#) a) (qualifyPortGraph a x) x"
  proof
    show "renameNode (drop 1) ` set (pg_nodes (qualifyPortGraph a x)) = set (pg_nodes x)"
      by (simp add: image_comp unqualifyNode_rename[symmetric] del: One_nat_def)
    show "set (pg_nodes (qualifyPortGraph a x)) = renameNode ((#) a) ` set (pg_nodes x)"
      by (simp add: qualifyNode_rename)
    show "renameEdge (drop 1) ` set (pg_edges (qualifyPortGraph a x)) = set (pg_edges x)"
      by (simp add: x image_comp unqualifyEdge_rename[symmetric] del: One_nat_def)
    show "set (pg_edges (qualifyPortGraph a x)) = renameEdge ((#) a) ` set (pg_edges x)"
      by (simp add: x qualifyEdge_rename)
    show "\<And>l. l \<in> node_name ` set (pg_nodes (qualifyPortGraph a x)) \<Longrightarrow> a # drop 1 l = l"
      by clarsimp
    show "\<And>l. l \<in> node_name ` set (pg_nodes x) \<Longrightarrow> drop 1 (a # l) = l"
      by simp
  qed
qed

text\<open>
  If we have one well-formed port graph and another port graph with the same node, edge and port
  lists that each have no duplicates, then the other port graph is equivalent to the former.
\<close>
lemma pgEquiv_permute:
  assumes "port_graph x"
      and "set (pg_nodes x) = set (pg_nodes y)"
      and "set (pg_edges x) = set (pg_edges y)"
      and "set (pg_ports x) = set (pg_ports y)"
      and "distinct (pg_nodes y)"
      and "distinct (pg_edges y)"
      and "distinct (pg_ports y)"
    shows "x \<approx> y"
  using assms port_graph_permute pgEquiv_witness_id by blast

(* Constructions helpful in equivalence proofs *)
(* TODO doc *)
(* TODO I'd love it if these could be unified even more *)

lemma pgEquiv_witness_combine_2:
  assumes "port_graph x"
      and "port_graph y"
      and "pg_disjoint x y"
    fixes f_x f_y
  defines "f \<equiv> \<lambda>p.
    if p \<in> set (map node_name (pg_nodes x))
      then f_x p
      else if p \<in> set (map node_name (pg_nodes y))
        then f_y p
        else undefined"
    shows "\<And>n. n \<in> set (pg_nodes x) \<Longrightarrow> renameNode f n = renameNode f_x n"
      and "\<And>n. n \<in> set (pg_nodes y) \<Longrightarrow> renameNode f n = renameNode f_y n"
      and "\<And>p. p \<in> set (pgraphPlaces x) \<Longrightarrow> renamePlace f p = renamePlace f_x p"
      and "\<And>p. p \<in> set (pgraphPlaces y) \<Longrightarrow> renamePlace f p = renamePlace f_y p"
      and "renameEdge f ` set (pg_edges x) = renameEdge f_x ` set (pg_edges x)"
      and "renameEdge f ` set (pg_edges y) = renameEdge f_y ` set (pg_edges y)"
proof -
  interpret x: port_graph x using assms by simp
  interpret y: port_graph y using assms by simp

  show renameNode_f_x:
    "n \<in> set (pg_nodes x) \<Longrightarrow> renameNode f n = renameNode f_x n" for n
    by (clarsimp simp add: f_def renameNode_def)
  show renameNode_f_y:
    "n \<in> set (pg_nodes y) \<Longrightarrow> renameNode f n = renameNode f_y n" for n
    using assms(3)
    by (metis (no_types, opaque_lifting) pg_disjoint_setD f_def image_eqI list.set_map renameNode_def sym_pg_disjoint)

  show renamePlace_f_x:
    "renamePlace f p = renamePlace f_x p" if p: "p \<in> set (pgraphPlaces x)" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes x)"
      using p True by (metis nodePlacesE pgraphPlaces_ground)
    ultimately show ?thesis
      by (simp add: f_def)
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed
  show renamePlace_f_y:
    "renamePlace f p = renamePlace f_y p" if p: "p \<in> set (pgraphPlaces y)" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes y)" and "node_name n \<notin> node_name ` set (pg_nodes x)"
      using p assms(3) True
      by (metis pg_disjoint_setD nodePlacesE pgraphPlaces_ground sym_pg_disjoint)
    ultimately show ?thesis
      by (simp add: f_def)
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed

  show renameEdge_f_x:
    "renameEdge f ` set (pg_edges x) = renameEdge f_x ` set (pg_edges x)"
    using x.edge_to_pg x.edge_from_pg by safe (simp_all add: renameEdge_def renamePlace_f_x)
  show renameEdge_f_y:
    "renameEdge f ` set (pg_edges y) = renameEdge f_y ` set (pg_edges y)"
    using y.edge_to_pg y.edge_from_pg by safe (simp_all add: renameEdge_def renamePlace_f_y)
qed

lemma pgEquiv_witness_combine_3:
  assumes "port_graph x"
      and "port_graph y"
      and "port_graph z"
      and "pg_disjoint x y"
      and "pg_disjoint y z"
      and "pg_disjoint x z"
    fixes f_x f_y f_z
  defines "f \<equiv> \<lambda>p.
    if p \<in> set (map node_name (pg_nodes x))
      then f_x p
      else if p \<in> set (map node_name (pg_nodes y))
        then f_y p
        else if p \<in> set (map node_name (pg_nodes z))
          then f_z p
          else undefined"
    shows "\<And>n. n \<in> set (pg_nodes x) \<Longrightarrow> renameNode f n = renameNode f_x n"
      and "\<And>n. n \<in> set (pg_nodes y) \<Longrightarrow> renameNode f n = renameNode f_y n"
      and "\<And>n. n \<in> set (pg_nodes z) \<Longrightarrow> renameNode f n = renameNode f_z n"
      and "\<And>p. p \<in> set (pgraphPlaces x) \<Longrightarrow> renamePlace f p = renamePlace f_x p"
      and "\<And>p. p \<in> set (pgraphPlaces y) \<Longrightarrow> renamePlace f p = renamePlace f_y p"
      and "\<And>p. p \<in> set (pgraphPlaces z) \<Longrightarrow> renamePlace f p = renamePlace f_z p"
      and "renameEdge f ` set (pg_edges x) = renameEdge f_x ` set (pg_edges x)"
      and "renameEdge f ` set (pg_edges y) = renameEdge f_y ` set (pg_edges y)"
      and "renameEdge f ` set (pg_edges z) = renameEdge f_z ` set (pg_edges z)"
proof -
  interpret x: port_graph x using assms by simp
  interpret y: port_graph y using assms by simp
  interpret z: port_graph z using assms by simp

  show renameNode_f_x:
    "n \<in> set (pg_nodes x) \<Longrightarrow> renameNode f n = renameNode f_x n" for n
    by (clarsimp simp add: f_def renameNode_def)
  show renameNode_f_y:
    "n \<in> set (pg_nodes y) \<Longrightarrow> renameNode f n = renameNode f_y n" for n
    using assms(4)
    by (metis (no_types, opaque_lifting) pg_disjoint_setD f_def image_eqI list.set_map renameNode_def sym_pg_disjoint)
  show renameNode_f_z:
    "n \<in> set (pg_nodes z) \<Longrightarrow> renameNode f n = renameNode f_z n" for n
    using assms(4,5,6)
    by (metis (no_types, opaque_lifting) pg_disjoint_setD f_def image_eqI list.set_map renameNode_def sym_pg_disjoint)

  show renamePlace_f_x:
    "renamePlace f p = renamePlace f_x p" if p: "p \<in> set (pgraphPlaces x)" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes x)"
      using p True by (metis nodePlacesE pgraphPlaces_ground)
    ultimately show ?thesis
      by (simp add: f_def)
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed
  show renamePlace_f_y:
    "renamePlace f p = renamePlace f_y p" if p: "p \<in> set (pgraphPlaces y)" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes y)" and "node_name n \<notin> node_name ` set (pg_nodes x)"
      using p assms(4) True
      by (metis pg_disjoint_setD nodePlacesE pgraphPlaces_ground sym_pg_disjoint)
    ultimately show ?thesis
      by (simp add: f_def)
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed
  show renamePlace_f_z:
    "renamePlace f p = renamePlace f_z p" if p: "p \<in> set (pgraphPlaces z)" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes z)" and "node_name n \<notin> node_name ` set (pg_nodes x)"
        and "node_name n \<notin> node_name ` set (pg_nodes y)"
      using p assms(4,5,6) True
      by (metis pg_disjoint_setD nodePlacesE pgraphPlaces_ground sym_pg_disjoint)
    ultimately show ?thesis
      by (simp add: f_def)
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed

  show renameEdge_f_x:
    "renameEdge f ` set (pg_edges x) = renameEdge f_x ` set (pg_edges x)"
    using x.edge_to_pg x.edge_from_pg by safe (simp_all add: renameEdge_def renamePlace_f_x)
  show renameEdge_f_y:
    "renameEdge f ` set (pg_edges y) = renameEdge f_y ` set (pg_edges y)"
    using y.edge_to_pg y.edge_from_pg by safe (simp_all add: renameEdge_def renamePlace_f_y)
  show renameEdge_f_z:
    "renameEdge f ` set (pg_edges z) = renameEdge f_z ` set (pg_edges z)"
    using z.edge_to_pg z.edge_from_pg by safe (simp_all add: renameEdge_def renamePlace_f_z)
qed

lemma pgEquiv_witness_combine_4:
  assumes "port_graph x"
      and "port_graph y"
      and "port_graph u"
      and "port_graph v"
      and "pg_disjoint x y"
      and "pg_disjoint x u"
      and "pg_disjoint x v"
      and "pg_disjoint y u"
      and "pg_disjoint y v"
      and "pg_disjoint u v"
    fixes f_x f_y f_u f_v
  defines "f \<equiv> \<lambda>p.
    if p \<in> set (map node_name (pg_nodes x))
      then f_x p
      else if p \<in> set (map node_name (pg_nodes y))
        then f_y p
        else if p \<in> set (map node_name (pg_nodes u))
          then f_u p
          else if p \<in> set (map node_name (pg_nodes v))
            then f_v p
            else undefined"
    shows "\<And>n. n \<in> set (pg_nodes x) \<Longrightarrow> renameNode f n = renameNode f_x n"
      and "\<And>n. n \<in> set (pg_nodes y) \<Longrightarrow> renameNode f n = renameNode f_y n"
      and "\<And>n. n \<in> set (pg_nodes u) \<Longrightarrow> renameNode f n = renameNode f_u n"
      and "\<And>n. n \<in> set (pg_nodes v) \<Longrightarrow> renameNode f n = renameNode f_v n"
      and "\<And>p. p \<in> set (pgraphPlaces x) \<Longrightarrow> renamePlace f p = renamePlace f_x p"
      and "\<And>p. p \<in> set (pgraphPlaces y) \<Longrightarrow> renamePlace f p = renamePlace f_y p"
      and "\<And>p. p \<in> set (pgraphPlaces u) \<Longrightarrow> renamePlace f p = renamePlace f_u p"
      and "\<And>p. p \<in> set (pgraphPlaces v) \<Longrightarrow> renamePlace f p = renamePlace f_v p"
      and "renameEdge f ` set (pg_edges x) = renameEdge f_x ` set (pg_edges x)"
      and "renameEdge f ` set (pg_edges y) = renameEdge f_y ` set (pg_edges y)"
      and "renameEdge f ` set (pg_edges u) = renameEdge f_u ` set (pg_edges u)"
      and "renameEdge f ` set (pg_edges v) = renameEdge f_v ` set (pg_edges v)"
proof -
  interpret x: port_graph x using assms by simp
  interpret y: port_graph y using assms by simp
  interpret u: port_graph u using assms by simp
  interpret v: port_graph v using assms by simp

  show renameNode_f_x:
    "n \<in> set (pg_nodes x) \<Longrightarrow> renameNode f n = renameNode f_x n" for n
    by (clarsimp simp add: f_def renameNode_def)
  show renameNode_f_y:
    "n \<in> set (pg_nodes y) \<Longrightarrow> renameNode f n = renameNode f_y n" for n
    using assms(5)
    by (metis (no_types, opaque_lifting) pg_disjoint_setD f_def image_eqI list.set_map renameNode_def sym_pg_disjoint)
  show renameNode_f_u:
    "n \<in> set (pg_nodes u) \<Longrightarrow> renameNode f n = renameNode f_u n" for n
    using assms(5,6,8)
    by (metis (no_types, opaque_lifting) pg_disjoint_setD f_def image_eqI list.set_map renameNode_def sym_pg_disjoint)
  show renameNode_f_v:
    "n \<in> set (pg_nodes v) \<Longrightarrow> renameNode f n = renameNode f_v n" for n
    using assms(5-10)
    by (metis (no_types, opaque_lifting) pg_disjoint_setD f_def image_eqI list.set_map renameNode_def sym_pg_disjoint)

  show renamePlace_f_x:
    "renamePlace f p = renamePlace f_x p" if p: "p \<in> set (pgraphPlaces x)" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes x)"
      using p True by (metis nodePlacesE pgraphPlaces_ground)
    ultimately show ?thesis
      by (simp add: f_def)
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed
  show renamePlace_f_y:
    "renamePlace f p = renamePlace f_y p" if p: "p \<in> set (pgraphPlaces y)" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes y)" and "node_name n \<notin> node_name ` set (pg_nodes x)"
      using p assms(5) True
      by (metis pg_disjoint_setD nodePlacesE pgraphPlaces_ground sym_pg_disjoint)
    ultimately show ?thesis
      by (simp add: f_def)
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed
  show renamePlace_f_u:
    "renamePlace f p = renamePlace f_u p" if p: "p \<in> set (pgraphPlaces u)" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes u)" and "node_name n \<notin> node_name ` set (pg_nodes x)"
        and "node_name n \<notin> node_name ` set (pg_nodes y)"
      using p assms(5,6,8) True
      by (metis pg_disjoint_setD nodePlacesE pgraphPlaces_ground sym_pg_disjoint)
    ultimately show ?thesis
      by (simp add: f_def)
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed
  show renamePlace_f_v:
    "renamePlace f p = renamePlace f_v p" if p: "p \<in> set (pgraphPlaces v)" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes v)" and "node_name n \<notin> node_name ` set (pg_nodes x)"
        and "node_name n \<notin> node_name ` set (pg_nodes y)" and "node_name n \<notin> node_name ` set (pg_nodes u)"
      using p assms(5-10) True
      by (metis pg_disjoint_setD nodePlacesE pgraphPlaces_ground sym_pg_disjoint)
    ultimately show ?thesis
      by (simp add: f_def)
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed

  show renameEdge_f_x:
    "renameEdge f ` set (pg_edges x) = renameEdge f_x ` set (pg_edges x)"
    using x.edge_to_pg x.edge_from_pg by safe (simp_all add: renameEdge_def renamePlace_f_x)
  show renameEdge_f_y:
    "renameEdge f ` set (pg_edges y) = renameEdge f_y ` set (pg_edges y)"
    using y.edge_to_pg y.edge_from_pg by safe (simp_all add: renameEdge_def renamePlace_f_y)
  show renameEdge_f_u:
    "renameEdge f ` set (pg_edges u) = renameEdge f_u ` set (pg_edges u)"
    using u.edge_to_pg u.edge_from_pg by safe (simp_all add: renameEdge_def renamePlace_f_u)
  show renameEdge_f_v:
    "renameEdge f ` set (pg_edges v) = renameEdge f_v ` set (pg_edges v)"
    using v.edge_to_pg v.edge_from_pg by safe (simp_all add: renameEdge_def renamePlace_f_v)
qed

end
