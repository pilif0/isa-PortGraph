theory PortGraphTrans
  imports PortGraph
begin

section\<open>Port Graph Transition System\<close>

text\<open>
  This section builds a transition system for port graphs.
  The transitions work by progressively removing nodes with no incoming edges from other nodes.
\<close>

subsection\<open>Node Flow\<close>

text\<open>Node flow of a port graph relates two nodes if the first has an edge going to the second\<close>
inductive node_flow :: "('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) node \<Rightarrow> ('s, 'a, 'p, 'l) node \<Rightarrow> bool"
  where
  edge: "\<lbrakk>x \<in> set (pg_nodes G); y \<in> set (pg_nodes G);
      e \<in> set (pg_edges G); edge_from e \<in> set (nodePlaces x); edge_to e \<in> set (nodePlaces y)\<rbrakk>
    \<Longrightarrow> node_flow G x y"
hide_fact (open) edge

text\<open>For well-formed port graphs we can compute the extent of the flow as a set of pairs.\<close>
lemma (in port_graph) node_flow_extent:
  " {(x, y). node_flow G x y} =
    set (map (\<lambda>e. (the (attachedTo (edge_from e)), the (attachedTo (edge_to e))))
      (filter (\<lambda>e. place_ground (edge_from e) \<and> place_ground (edge_to e))
        (pg_edges G)))" (is "_ = set (map ?f (filter ?P (pg_edges G)))")
proof safe
  fix a b
  assume flow_ab: "node_flow G a b"

  have node_a: "a \<in> set (pg_nodes G)"
    using flow_ab node_flow.cases by blast
  have node_b: "b \<in> set (pg_nodes G)"
    using flow_ab node_flow.cases by blast
  obtain e
    where "e \<in> set (pg_edges G)"
      and "edge_from e \<in> set (nodePlaces a)"
      and "edge_to e \<in> set (nodePlaces b)"
    using flow_ab node_flow.cases by blast
  note e = this

  note e(1)
  moreover have "place_ground (edge_from e)"
    using e(2) node_a attachedToI attachedTo_SomeE by blast
  moreover have "place_ground (edge_to e)"
    using e(3) node_b attachedToI attachedTo_SomeE by blast
  ultimately have "e \<in> set (filter ?P (pg_edges G))"
    by simp
  moreover have "attachedTo (edge_from e) = Some a"
    using e(2) node_a attachedToI by blast
  moreover have "attachedTo (edge_to e) = Some b"
    using e(3) node_b attachedToI by blast
  ultimately show "(a, b) \<in> set (map ?f (filter ?P (pg_edges G)))"
    by (metis (no_types, lifting) in_set_conv_nth length_map nth_map option.sel)
next
  fix a b
  assume set_ab: "(a, b) \<in> set (map ?f (filter ?P (pg_edges G)))"
  then obtain e
    where "e \<in> set (pg_edges G)"
      and "attachedTo (edge_from e) = Some a"
      and "attachedTo (edge_to e) = Some b"
    by clarsimp (metis edge_from_pg edge_to_pg groundPort_attached_obtain option.sel)
  note e = this

  show "node_flow G a b"
  proof (intro node_flow.intros)
    show "a \<in> set (pg_nodes G)" using e(2) by simp
    show "b \<in> set (pg_nodes G)" using e(3) by simp
    show "e \<in> set (pg_edges G)" using e(1) .
    show "edge_from e \<in> set (nodePlaces a)" using e(1,2) attachedTo_nodePlaces edge_from_pg by blast
    show "edge_to e \<in> set (nodePlaces b)" using e(1,3) attachedTo_nodePlaces edge_to_pg by blast
  qed
qed

subsubsection\<open>Node Flow and Qualification\<close>

text\<open>Node flow for a qualified port graph determines the flow for its unqualified version.\<close>
lemma node_flow_qualify_imp_unqualify:
  assumes "node_flow (qualifyPortGraph a G) x y"
    shows "node_flow G (unqualifyNode 1 x) (unqualifyNode 1 y)"
proof -
  obtain e
    where "x \<in> set (pg_nodes (qualifyPortGraph a G))"
      and "y \<in> set (pg_nodes (qualifyPortGraph a G))"
      and "e \<in> set (pg_edges (qualifyPortGraph a G))"
      and "edge_from e \<in> set (nodePlaces x)"
      and "edge_to e \<in> set (nodePlaces y)"
    using assms node_flow.cases by metis
  then show ?thesis
    by (fastforce simp del: One_nat_def intro: node_flow.edge[where e = "unqualifyEdge 1 e"])
qed

text\<open>Conversely, node flow in a port graph induces the flow in its version qualified by any atom\<close>
lemma node_flow_imp_qualify:
  assumes "node_flow G x y"
    shows "node_flow (qualifyPortGraph a G) (qualifyNode a x) (qualifyNode a y)"
  using assms by (fastforce elim: node_flow.cases intro: node_flow.edge)

text\<open>As such, node flow is not affected by qualification of port graphs\<close>
lemma node_flow_qualifyPortGraph:
  "node_flow (qualifyPortGraph a G) (qualifyNode a x) (qualifyNode a y) = node_flow G x y"
  using node_flow_qualify_imp_unqualify node_flow_imp_qualify unqualify_qualify_node_inv by metis

subsubsection\<open>Acyclic Node Flow\<close>

text\<open>Node flow's extent is a subset of pairs of nodes of the relevant port graph\<close>
lemma node_flow_subset_nodes:
  "{(x, y). node_flow G x y} \<subseteq> {(x, y). x \<in> set (pg_nodes G) \<and> y \<in> set (pg_nodes G)}"
proof clarsimp
  fix a b
  show "node_flow G a b \<Longrightarrow> a \<in> set (pg_nodes G) \<and> b \<in> set (pg_nodes G)"
    by (cases G a b rule: node_flow.cases ; simp)
qed

text\<open>Node flow's extent is finite, since node sets are finite\<close>
lemma finite_node_flow:
  "finite {(x, y). node_flow G x y}"
proof -
  have "finite {(x, y). x \<in> set (pg_nodes G) \<and> y \<in> set (pg_nodes G)}"
    by clarsimp
  then show ?thesis
    using node_flow_subset_nodes by (metis finite_subset)
qed

text\<open>Thanks to its finiteness, any acyclic node flow is well-founded\<close>
lemma wf_acyclic_node_flow:
  "acyclicP (node_flow G) \<Longrightarrow> wf {(x, y). node_flow G x y}"
  by (subst wf_iff_acyclic_if_finite[OF finite_node_flow])

(* TODO Is acyclicity of flow preserved through qualification? It should be. *)

text\<open>
  For any port graph with nodes and acyclic node flow, there exists a node of that port graph with
  no incoming edge from any other node.
  It is essentially the ``minimum'' of the flow.
\<close>
lemma (in port_graph) node_no_in_ex:
  assumes "pg_nodes G \<noteq> []"
      and "acyclicP (node_flow G)"
  obtains n
    where "n \<in> set (pg_nodes G)"
      and "\<forall>e. e \<in> set (pg_edges G) \<and> place_ground (edge_from e) \<longrightarrow> edge_to e \<notin> set (nodePlaces n)"
proof -
  have "wf {(x, y). node_flow G x y}"
    using wf_acyclic_node_flow assms(2) by metis
  moreover obtain n where "n \<in> set (pg_nodes G)"
    using assms by fastforce
  ultimately obtain z
    where "z \<in> set (pg_nodes G)"
      and "\<And>y. (y, z) \<in> {(x, y). node_flow G x y} \<Longrightarrow> y \<notin> set (pg_nodes G)"
    using wfE_min by metis
  then show ?thesis
    using that
    by (metis case_prodI edge_from_pg mem_Collect_eq node_flow.intros pgraphPlaces_ground)
qed

subsection\<open>Node Removal\<close>

text\<open>Remove a node from a port graph, including any edges adjacent on its places\<close>
definition removeNode :: "('s, 'a, 'p, 'l) node \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) port_graph"
  where "removeNode n G =
  PGraph
    (filter ((\<noteq>) n) (pg_nodes G))
    (disconnectFromPlaces (nodePlaces n) (pg_edges G))
    (pg_ports G)"

lemma removeNode_simps [simp]:
  "pg_nodes (removeNode n G) = filter ((\<noteq>) n) (pg_nodes G)"
  "pg_edges (removeNode n G) = (disconnectFromPlaces (nodePlaces n) (pg_edges G))"
  "pg_ports (removeNode n G) = pg_ports G"
  by (simp_all add: removeNode_def)

text\<open>Removing a node preserves well-formedness of a port graph\<close>
lemma port_graph_removeNode:
  assumes "port_graph x"
    shows "port_graph (removeNode n x)"
proof -
  interpret x: port_graph x using assms(1) .

  show ?thesis
  proof
    show "edge_from e \<in> set (pgraphPlaces (removeNode n x))"
      if "e \<in> set (pg_edges (removeNode n x))" for e
      using x.edge_from_pg that
      by (fastforce elim: disconnectFromPlaces_in_setE simp add: removeNode_def)
    show "edge_to e \<in> set (pgraphPlaces (removeNode n x))"
      if "e \<in> set (pg_edges (removeNode n x))" for e
      using x.edge_to_pg that
      by (fastforce elim: disconnectFromPlaces_in_setE simp add: removeNode_def)
    show "m = m'"
      if "m \<in> set (pg_nodes (removeNode n x))" and "m' \<in> set (pg_nodes (removeNode n x))"
        and "node_name m = node_name m'"
      for m m'
      using x.node_unique_path that by (simp add: removeNode_def)
    show " port.index p
         < length (filter (\<lambda>x. port.side x = port.side p) (pg_ports (removeNode n x)))"
      if "p \<in> set (pg_ports (removeNode n x))"
      for p
      using x.ports_index_bound that by simp
    show "port.label p = port.label q"
      if "p \<in> set (pg_ports (removeNode n x))" and "q \<in> set (pg_ports (removeNode n x))"
        and "port.side p = port.side q" and "port.index p = port.index q"
      for p q
      using x.open_ports_label_eq that by (subst (asm) (1 2) removeNode_simps) blast
    show "port.label p = port.label q"
      if "m \<in> set (pg_nodes (removeNode n x))" and "p \<in> set (node_ports m)"
        and "q \<in> set (node_ports m)" and "port.side p = port.side q"
        and "port.index p = port.index q"
      for m p q
      using x.node_ports_label_eq that by (simp add: removeNode_def) blast
    show "distinct (pg_nodes (removeNode n x))"
      using x.nodes_distinct by (simp add: removeNode_def)
    show "distinct (pg_edges (removeNode n x))"
      using x.edges_distinct by (simp add: removeNode_def disconnectFromPlaces_def)
    show "distinct (pg_ports (removeNode n x))"
      using x.ports_distinct by simp
  qed
qed

text\<open>Removing a node preserves well-formed flow of a port graph\<close>
lemma port_graph_flow_removeNode:
  assumes "port_graph_flow x"
    shows "port_graph_flow (removeNode n x)"
proof -
  interpret x: port_graph_flow x using assms(1) .
  interpret port_graph "removeNode n x" using port_graph_removeNode x.port_graph_axioms by metis

  show ?thesis
  proof
    show "place_side (edge_from e) = In"
      if "e \<in> set (pg_edges (removeNode n x))" and "edge_in_flow e" and "place_open (edge_from e)"
      for e
      using x.edge_from_open that by (simp add: removeNode_def disconnectFromPlaces_def)
    show "place_side (edge_to e) = Out"
      if "e \<in> set (pg_edges (removeNode n x))" and "edge_in_flow e" and "place_open (edge_to e)"
      for e
      using x.edge_to_open that by (simp add: removeNode_def disconnectFromPlaces_def)
    show "place_side (edge_from e) = Out"
      if "e \<in> set (pg_edges (removeNode n x))" and "edge_in_flow e" and "place_ground (edge_from e)"
      for e
      using x.edge_from_ground that by (simp add: removeNode_def disconnectFromPlaces_def)
    show "place_side (edge_to e) = In"
      if "e \<in> set (pg_edges (removeNode n x))" and "edge_in_flow e" and "place_ground (edge_to e)"
      for e
      using x.edge_to_ground that by (simp add: removeNode_def disconnectFromPlaces_def)
  qed
qed

subsection\<open>Enabled Node\<close>

text\<open>
  Given a port graph, a node is enabled if and only if it is in that port graph and it has no
  incoming edges from other nodes of that port graph.
\<close>
definition nodeEnabled :: "('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) node \<Rightarrow> bool"
  where "nodeEnabled G n =
  ( n \<in> set (pg_nodes G) \<and>
    (\<forall>e. e \<in> set (pg_edges G) \<and> place_ground (edge_from e) \<longrightarrow> edge_to e \<notin> set (nodePlaces n)))"

text\<open>Any port graph with nodes and acyclic node flow has some enabled node\<close>
lemma (in port_graph) node_enabled_obtain:
  assumes "pg_nodes G \<noteq> []"
      and "acyclicP (node_flow G)"
  obtains n where "nodeEnabled G n"
  using assms node_no_in_ex nodeEnabled_def by metis

subsection\<open>Transition\<close>

text\<open>
  There exists a transition between two port graphs annotated by a node if the second port graph is
  the result of removing that node from the first
\<close>
inductive pgTrans :: "('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) node \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> bool"
  where "\<lbrakk>nodeEnabled G n; G' = removeNode n G\<rbrakk> \<Longrightarrow> pgTrans G n G'"

text\<open>No port graph without nodes can transition\<close>
lemma
  assumes "pg_nodes G = []"
      and "pgTrans G n G'"
    shows False
  using assms by (clarsimp elim!: pgTrans.cases simp add: nodeEnabled_def)

text\<open>Given a transition, the labelling node will not be in the resulting port graph\<close>
lemma pgTrans_node_removed:
  assumes "pgTrans G n G'"
  shows "n \<notin> set (pg_nodes G')"
  using assms by (clarsimp elim!: pgTrans.cases simp add: removeNode_def)

(* TODO That means that eventually you will run out of nodes, leading to a kind of termination. *)

(* Equivalence gives a kind of bisimulation up to label renaming *)
text\<open>
  Given two equivalent well-formed port graphs, a transition on one determines a transition on the
  other
\<close>
lemma (* TODO this would be a better form of the theorem below *)
    fixes X Y X' :: "('a, 'b, 'c, 'd) port_graph"
  assumes "X \<approx> Y"
      and "pgEquiv_witness f g X Y"
      and "port_graph X"
      and "pgTrans X n X'"
  obtains Y' where "pgTrans Y (renameNode f n) Y'" and "X' \<approx> Y'"
proof -
  obtain g
    where "renameNode f ` (set (pg_nodes X)) = set (pg_nodes Y)"
      and "set (pg_nodes X) = renameNode g ` (set (pg_nodes Y))"
      and "renameEdge f ` (set (pg_edges X)) = set (pg_edges Y)"
      and "set (pg_edges X) = renameEdge g ` (set (pg_edges Y))"
      and "set (pg_ports X) = set (pg_ports Y)"
      and "\<And>l. l \<in> node_name ` set (pg_nodes X) \<Longrightarrow> g (f l) = l"
      and "\<And>l. l \<in> node_name ` set (pg_nodes Y) \<Longrightarrow> f (g l) = l"
    using assms by (elim pgEquivE ; blast)
  note XY = this

  obtain Y' :: "('a, 'b, 'c, 'd) port_graph"
   where "pgTrans Y (renameNode f n) (removeNode (renameNode f n) Y)"
     and "X' \<approx> (removeNode (renameNode f n) Y)"
    using assms(4)
    apply (clarsimp elim!: pgTrans.cases)
    apply (rule that)
     apply (rule pgTrans.intros)
      apply (clarsimp simp add: nodeEnabled_def)
      apply (rule conjI)
    using XY(1) apply blast
      apply (clarsimp simp add: image_image)
    oops

lemma pgTrans_pgEquiv:
    fixes X Y X' :: "('a, 'b, 'c, 'd) port_graph"
  assumes "X \<approx> Y"
      and "port_graph X"
      and "pgTrans X n X'"
  obtains f Y' where "pgTrans Y (renameNode f n) Y'" and "X' \<approx> Y'"
proof -
  interpret X: port_graph X using assms(2) .

  obtain f g
    where "renameNode f ` (set (pg_nodes X)) = set (pg_nodes Y)"
      and "set (pg_nodes X) = renameNode g ` (set (pg_nodes Y))"
      and "renameEdge f ` (set (pg_edges X)) = set (pg_edges Y)"
      and "set (pg_edges X) = renameEdge g ` (set (pg_edges Y))"
      and "set (pg_ports X) = set (pg_ports Y)"
      and "\<And>l. l \<in> node_name ` set (pg_nodes X) \<Longrightarrow> g (f l) = l"
      and "\<And>l. l \<in> node_name ` set (pg_nodes Y) \<Longrightarrow> f (g l) = l"
    using assms(1,2) by (elim pgEquivE ; blast)
  note fg = this

  have enabled_X: "nodeEnabled X n" and X': "X' = removeNode n X"
    using assms(3) by (metis pgTrans.cases)+

  have enabled_Y: "nodeEnabled Y (renameNode f n)"
  proof -
    have n_in: "n \<in> set (pg_nodes X)"
      using enabled_X nodeEnabled_def by metis
    then have "renameNode f n \<in> set (pg_nodes Y)"
      using fg(1) by blast
    moreover have "edge_to e \<notin> set (nodePlaces (renameNode f n))"
      if "e \<in> set (pg_edges Y)" and "place_ground (edge_from e)"
      for e
    proof -
      have "renameEdge g e \<in> set (pg_edges X)"
        using that(1) fg(4) by blast
      then have "edge_to (renameEdge g e) \<notin> set (nodePlaces n)"
        using enabled_X nodeEnabled_def that(2) by (metis renameEdge_simps(2) renamePlace_simps(3))
      then show ?thesis
        using n_in fg(6) by fastforce
    qed
    ultimately show ?thesis
      using nodeEnabled_def by metis
  qed
  then have "pgTrans Y (renameNode f n) (removeNode (renameNode f n) Y)"
    by (metis pgTrans.intros)
  moreover have "X' \<approx> (removeNode (renameNode f n) Y)"
    unfolding X'
  proof (intro pgEquivI pgEquiv_witnessI)
    show "port_graph (removeNode n X)"
      by (metis assms(2) port_graph_removeNode)
    then interpret rX: port_graph "removeNode n X" .

    have pg_Y: "port_graph Y"
      using assms(1,2) by blast
    then interpret Y: port_graph Y .

    show "port_graph (removeNode (renameNode f n) Y)"
      using pg_Y port_graph_removeNode by blast
    then interpret rY: port_graph "removeNode (renameNode f n) Y" .

    show "set (pg_ports (removeNode n X)) = set (pg_ports (removeNode (renameNode f n) Y))"
      by (simp add: fg(5))

    have "n = x" if "x \<in> set (pg_nodes X)" and "renameNode f n = renameNode f x" for x
      using that enabled_X fg(6)
      by (metis image_eqI nodeEnabled_def X.node_unique_path renameNode_simps(2))
    then show "renameNode f ` set (pg_nodes (removeNode n X)) = set (pg_nodes (removeNode (renameNode f n) Y))"
      using fg(1) by fastforce

    have "renameNode f n \<noteq> x" if "x \<in> set (pg_nodes Y)" and "n \<noteq> renameNode g x" for x
      using that enabled_X fg(6)
      by (metis image_eqI node.expand nodeEnabled_def renameNode_simps(2-4))
    then show "set (pg_nodes (removeNode n X)) = renameNode g ` set (pg_nodes (removeNode (renameNode f n) Y))"
      using fg(2,7) by (fastforce simp add: node.expand)

    have rn_in_Y: "renameNode f n \<in> set (pg_nodes Y)"
      using enabled_Y by (simp add: nodeEnabled_def)

    have n_in_X: "n \<in> set (pg_nodes X)"
      using enabled_X by (simp add: nodeEnabled_def)

    have inv_on_places_X:
      "p \<in> set (pgraphPlaces X) \<Longrightarrow> renamePlace g (renamePlace f p) = p" for p
      using fg(6) by fastforce
    then have inv_on_edges_X:
      "e \<in> set (pg_edges X) \<Longrightarrow> renameEdge g (renameEdge f e) = e" for e
      by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3) X.edge_from_pg X.edge_to_pg)

    have inv_on_places_Y:
      "p \<in> set (pgraphPlaces Y) \<Longrightarrow> renamePlace f (renamePlace g p) = p" for p
      using fg(7) by fastforce
    then have inv_on_edges_Y:
      "e \<in> set (pg_edges Y) \<Longrightarrow> renameEdge f (renameEdge g e) = e" for e
      by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3) Y.edge_from_pg Y.edge_to_pg)

    have rename_ground_place_X: False
      if rename: "renamePlace f pl = GroundPort (QPort p (f (node_name n)))"
        and p_n: "p \<in> set (node_ports n)"
        and pl_X: "pl \<in> set (pgraphPlaces X)"
        and pl_rX: "pl \<in> set (pgraphPlaces (removeNode n X))"
      for p pl
    proof -
      have ground: "place_ground pl"
        using rename renamePlace_simps(2) by fastforce

      have "place_name pl = node_name n"
      proof -
        have "pl = renamePlace g (renamePlace f pl)"
          using pl_X inv_on_places_X by metis
        then have "place_name pl = g (f (node_name n))"
          using rename by simp
        then show ?thesis
          using fg(6) n_in_X by simp
      qed
      moreover obtain m
        where m_in: "m \<in> set (pg_nodes X)"
          and m_neq_n: "m \<noteq> n"
          and "node_name m = place_name pl"
        using ground pl_rX by fastforce
      ultimately have "node_name m = node_name n"
        by metis
      then show False
        using m_in n_in_X m_neq_n X.node_unique_path by metis
    qed

    have rename_ground_place_Y: False
      if rename: "renamePlace g pl = GroundPort (QPort p (node_name n))"
        and p_n: "p \<in> set (node_ports n)"
        and pl_Y: "pl \<in> set (pgraphPlaces Y)"
        and pl_rY: "pl \<in> set (pgraphPlaces (removeNode (renameNode f n) Y))"
      for p pl
    proof -
      have ground: "place_ground pl"
        using rename renamePlace_simps(2) by fastforce

      have "place_name pl = f (node_name n)"
      proof -
        have "pl = renamePlace f (renamePlace g pl)"
          using pl_Y inv_on_places_Y by metis
        then show ?thesis
          using rename by simp
      qed
      moreover obtain m
        where m_in: "m \<in> set (pg_nodes Y)"
          and m_neq_n: "m \<noteq> renameNode f n"
          and "node_name m = place_name pl"
        using ground pl_rY by fastforce
      ultimately have "node_name m = f (node_name n)"
        by metis
      then show False
        using m_in rn_in_Y m_neq_n Y.node_unique_path by simp
    qed

    show "renameEdge f ` set (pg_edges (removeNode n X)) = set (pg_edges (removeNode (renameNode f n) Y))"
    proof safe
      fix e
      assume e: "e \<in> set (pg_edges (removeNode n X))"

      have "renameEdge f e \<in> set (pg_edges Y)"
        using e fg(3) by (fastforce simp add: disconnectFromPlaces_def)
      moreover have False
        if "renamePlace f (edge_from e) = GroundPort (QPort p (f (node_name n)))"
          and "p \<in> set (node_ports n)"
        for p
        using that e X.edge_from_pg rX.edge_from_pg rename_ground_place_X
        by (metis disconnectFromPlaces_in_setE removeNode_simps(2))
      moreover have False
        if "renamePlace f (edge_to e) = GroundPort (QPort p (f (node_name n)))"
          and "p \<in> set (node_ports n)"
        for p
        using that e X.edge_to_pg rX.edge_to_pg rename_ground_place_X
        by (metis disconnectFromPlaces_in_setE removeNode_simps(2))
      ultimately show "renameEdge f e \<in> set (pg_edges (removeNode (renameNode f n) Y))"
        by (simp add: removeNode_def disconnectFromPlaces_def) blast
    next
      fix e
      assume e: "e \<in> set (pg_edges (removeNode (renameNode f n) Y))"

      have "e = renameEdge f (renameEdge g e)"
        using e inv_on_edges_Y
        by (metis disconnectFromPlaces_in_setE removeNode_simps(2))
      moreover have "renameEdge g e \<in> set (pg_edges X)"
        using e fg(4)
        by (metis disconnectFromPlaces_in_setE image_iff removeNode_simps(2))
      moreover have False
        if "renamePlace g (edge_from e) = GroundPort (QPort p (node_name n))"
          and "p \<in> set (node_ports n)"
        for p
        using that e Y.edge_from_pg rY.edge_from_pg rename_ground_place_Y
        by (metis disconnectFromPlaces_in_setE removeNode_simps(2))
      moreover have False
        if "renamePlace g (edge_to e) = GroundPort (QPort p (node_name n))"
          and "p \<in> set (node_ports n)"
        for p
        using that e Y.edge_to_pg rY.edge_to_pg rename_ground_place_Y
        by (metis disconnectFromPlaces_in_setE removeNode_simps(2))
      ultimately show "e \<in> renameEdge f ` set (pg_edges (removeNode n X))"
        by (fastforce simp add: disconnectFromPlaces_def)
    qed

    show "set (pg_edges (removeNode n X)) = renameEdge g ` set (pg_edges (removeNode (renameNode f n) Y))"
    proof safe
      fix e
      assume e: "e \<in> set (pg_edges (removeNode (renameNode f n) Y))"

      have "renameEdge g e \<in> set (pg_edges X)"
        using e fg(4) by (fastforce simp add: disconnectFromPlaces_def)
      moreover have False
        if "renamePlace g (edge_from e) = GroundPort (QPort p (node_name n))"
          and "p \<in> set (node_ports n)"
        for p
        using that e Y.edge_from_pg rY.edge_from_pg rename_ground_place_Y
        by (metis disconnectFromPlaces_in_setE removeNode_simps(2))
      moreover have False
        if "renamePlace g (edge_to e) = GroundPort (QPort p (node_name n))"
          and "p \<in> set (node_ports n)"
        for p
        using that e Y.edge_to_pg rY.edge_to_pg rename_ground_place_Y
        by (metis disconnectFromPlaces_in_setE removeNode_simps(2))
      ultimately show "renameEdge g e \<in> set (pg_edges (removeNode n X))"
        by (simp add: removeNode_def disconnectFromPlaces_def) blast
    next
      fix e
      assume e: "e \<in> set (pg_edges (removeNode n X))"

      have "e = renameEdge g (renameEdge f e)"
        using e inv_on_edges_X
        by (metis disconnectFromPlaces_in_setE removeNode_simps(2))
      moreover have "renameEdge f e \<in> set (pg_edges Y)"
        using e fg(3)
        by (metis disconnectFromPlaces_in_setE image_iff removeNode_simps(2))
      moreover have False
        if "renamePlace f (edge_from e) = GroundPort (QPort p (f (node_name n)))"
          and "p \<in> set (node_ports n)"
        for p
        using that e X.edge_from_pg rX.edge_from_pg rename_ground_place_X
        by (metis disconnectFromPlaces_in_setE removeNode_simps(2))
      moreover have False
        if "renamePlace f (edge_to e) = GroundPort (QPort p (f (node_name n)))"
          and "p \<in> set (node_ports n)"
        for p
        using that e X.edge_to_pg rX.edge_to_pg rename_ground_place_X
        by (metis disconnectFromPlaces_in_setE removeNode_simps(2))
      ultimately show "e \<in> renameEdge g ` set (pg_edges (removeNode (renameNode f n) Y))"
        by (fastforce simp add: disconnectFromPlaces_def)
    qed
    show "\<And>l. l \<in> node_name ` set (pg_nodes (removeNode n X)) \<Longrightarrow> g (f l) = l"
      using fg(6) by (fastforce simp add: removeNode_def)
    show "\<And>l. l \<in> node_name ` set (pg_nodes (removeNode (renameNode f n) Y)) \<Longrightarrow> f (g l) = l"
      using fg(7) by (fastforce simp add: removeNode_def)
  qed
  ultimately show thesis
    by (rule that)
qed

text\<open>
  Any node that is enabled after a transition (of a well-formed port graph) must have had all of its
  incoming edges from other nodes be from the removed node.
  (If it was already enabled then this is trivial, as there already were no such edges.)
\<close>
lemma nodeEnabled_after_pgTrans:
  assumes "pgTrans G n G'"
      and "nodeEnabled G' x"
      and "port_graph G"
      and e_in: "e \<in> set (pg_edges G)"
      and e_to: "edge_to e \<in> set (nodePlaces x)"
      and ground: "place_ground (edge_from e)"
    shows "edge_from e \<in> set (nodePlaces n)"
proof -
  have G': "G' = removeNode n G"
    using assms(1) by (blast elim: pgTrans.cases)

  have x_G': "x \<in> set (pg_nodes G')"
    using assms(2) by (simp add: nodeEnabled_def)
  then have x_G: "x \<in> set (pg_nodes G)"
    using assms(1) G' by simp

  have n_G: "n \<in> set (pg_nodes G)"
    using assms(1) by (clarsimp elim!: pgTrans.cases simp add: nodeEnabled_def)

  have "n \<notin> set (pg_nodes G')"
    using assms(1) pgTrans_node_removed by blast
  then have "x \<noteq> n"
    using x_G' by blast
  then have distinct_path_x_n: "node_name x \<noteq> node_name n"
    using assms(3) x_G n_G port_graph.node_unique_path by blast

  have "e \<notin> set (pg_edges G')"
    using assms(2) e_in e_to ground by (fastforce simp add: nodeEnabled_def)
  moreover have "edge_to e \<notin> (\<lambda>p. GroundPort (QPort p (node_name n))) ` set (node_ports n)"
    using e_to distinct_path_x_n by clarsimp
  ultimately show ?thesis
    using e_in by (simp add: G' disconnectFromPlaces_def)
qed

subsection\<open>Bisimulation\<close>

text\<open>
  Based on the transitions we define the usual corecursive bisimulation relation, except we allow
  for renaming of the node labelling the transitions.
\<close>
coinductive bisim :: "('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> bool"
  where
    "\<lbrakk>\<And>p' n. pgTrans p n p' \<Longrightarrow> \<exists>q' f. pgTrans q (renameNode f n) q' \<and> bisim p' q';
      \<And>q' n. pgTrans q n q' \<Longrightarrow> \<exists>p' f. pgTrans p (renameNode f n) p' \<and> bisim p' q'\<rbrakk> \<Longrightarrow> bisim p q"

text\<open>In this way, equivalent (well-formed) port graphs are bisimilar\<close>
lemma bisim_pgEquiv:
  fixes X Y :: "('s, 'a, 'p, 'l) port_graph"
  assumes "X \<approx> Y"
      and "port_graph X"
    shows "bisim X Y"
proof -
  have pg_y: "port_graph Y"
    using assms by blast

  have stepA: "\<exists>y'. (\<exists>f. pgTrans y (renameNode f n) y') \<and> (x' \<approx> y' \<and> port_graph x' \<and> port_graph y' \<or> bisim x' y')"
    if "x \<approx> y" and "port_graph x" and "port_graph y" and "pgTrans x n x'"
    for x y x' :: "('s, 'a, 'p, 'l) port_graph" and n
    using that pgTrans_pgEquiv by (metis pgTrans.simps port_graph_removeNode)
  have stepB:  "\<exists>x'. (\<exists>f. pgTrans x (renameNode f n) x') \<and> (x' \<approx> y' \<and> port_graph x' \<and> port_graph y' \<or> bisim x' y')"
    if "x \<approx> y" and "port_graph x" and "port_graph y" and "pgTrans y n y'"
    for x y y' :: "('s, 'a, 'p, 'l) port_graph" and n
    using that pgTrans_pgEquiv by (metis pgTrans.simps port_graph_removeNode pgEquiv_sym)

  have "X \<approx> Y \<and> port_graph X \<and> port_graph Y"
    using assms pg_y by blast
  then show ?thesis
    by (coinduction arbitrary: X Y) (metis stepA stepB)
qed

end
