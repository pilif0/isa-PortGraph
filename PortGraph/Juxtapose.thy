theory Juxtapose
  imports PortGraph
begin

section\<open>Port Graph Juxtaposition\<close>

fun juxtapose :: "('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> ('s, 'a, 'p, 'l) port_graph"
  where "juxtapose P Q = PGraph
    (pg_nodes P @ pg_nodes Q)
    ( pg_edges P @
      map (shiftOpenInEdge
            (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports P)))
            (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports P))))
          (pg_edges Q)
    )
    ( pg_ports P @
      map (shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports P)))) (pg_ports Q)
    )"

text\<open>
  Every port in the result is either:
  \<^item> In the LHS port graph, or
  \<^item> A shifted input or output in RHS port graph, or
  \<^item> An unshifted other port in RHS port graph.
\<close>
lemma port_in_juxtapose:
  assumes "p \<in> set (pg_ports (juxtapose x y))"
  obtains
    (X) "p \<in> set (pg_ports x)"
  | (Y) p' where "p' \<in> set (pg_ports y)" and "p = shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) p'"
  using assms by simp (elim disjE ; blast)

text\<open>All the places of the LHS port graph are in their juxtaposition\<close>
lemma pgraphPlaces_first_in_juxtapose:
  "set (pgraphPlaces x) \<subseteq> set (pgraphPlaces (juxtapose x y))"
  by clarsimp

text\<open>All the places of the RHS port graph are in their juxtaposition, but possibly shifted\<close>
lemma pgraphPlaces_second_in_juxtapose:
  " (\<lambda>p.
      if place_open p
        then shiftOpenPlace (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) p
        else p) ` set (pgraphPlaces y) \<subseteq>
    set (pgraphPlaces (juxtapose x y))"
  by fastforce

text\<open>Nodes of juxtaposition are nodes of either component\<close>
lemma in_nodes_juxtaposeE:
  assumes "n \<in> set (pg_nodes (juxtapose x y))"
  obtains "n \<in> set (pg_nodes x)" | "n \<in> set (pg_nodes y)"
  using assms by fastforce

text\<open>Port graph is disjoint from juxtaposition if it is disjoint from each component\<close>
lemma pg_disjoint_juxtapose [simp]:
  "pg_disjoint (juxtapose x y) z = (pg_disjoint x z \<and> pg_disjoint y z)"
  "pg_disjoint z (juxtapose x y) = (pg_disjoint z x \<and> pg_disjoint z y)"
  by (fastforce simp add: pg_disjoint_def)+

text\<open>Juxtaposition of well-formed port graphs is well-formed\<close>
lemma port_graph_juxtapose:
    fixes x y :: "('s, 'a, 'p, 'l) port_graph"
  assumes "port_graph x"
      and "port_graph y"
      and "pg_disjoint x y"
    shows "port_graph (juxtapose x y)"
proof -
  interpret x: port_graph x using assms by simp
  interpret y: port_graph y using assms by simp

  (* Nested so every subgoal has access to x and y theorems *)
  show ?thesis
  proof
    fix e
    assume e: "e \<in> set (pg_edges (juxtapose x y))"
    then consider
      (X) "e \<in> set (pg_edges x)"
    | (Y) e' where "e = shiftOpenInEdge (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) e'"
        and "e' \<in> set (pg_edges y)"
      by simp blast
    note e_cases = this

    from e_cases show "edge_from e \<in> set (pgraphPlaces (juxtapose x y))"
    proof cases
      case X
      then show ?thesis
        using pgraphPlaces_first_in_juxtapose x.edge_from_pg by blast
    next
      case Y

      have
        " edge_from e
        \<in> (\<lambda>p. if place_open p
            then shiftOpenPlace (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) p
            else p) `
          set (pgraphPlaces y)"
      proof
        show
          " edge_from e
          = (if place_open (edge_from e')
              then shiftOpenPlace (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (edge_from e')
              else edge_from e')"
          using Y(1) by simp
        show "edge_from e' \<in> set (pgraphPlaces y)"
          using Y(2) y.edge_from_pg by metis
      qed
      then show ?thesis
        using pgraphPlaces_second_in_juxtapose by blast
    qed

    from e_cases show "edge_to e \<in> set (pgraphPlaces (juxtapose x y))"
    proof cases
      case X
      then show ?thesis
        using pgraphPlaces_first_in_juxtapose x.edge_to_pg by blast
    next
      case Y

      have
        " edge_to e
        \<in> (\<lambda>p. if place_open p
            then shiftOpenPlace (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) p
            else p) `
          set (pgraphPlaces y)"
      proof
        show
          " edge_to e
          = (if place_open (edge_to e')
              then shiftOpenPlace (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) (edge_to e')
              else edge_to e')"
          using Y(1) by simp
        show "edge_to e' \<in> set (pgraphPlaces y)"
          using Y(2) y.edge_to_pg by metis
      qed
      then show ?thesis
        using pgraphPlaces_second_in_juxtapose by blast
    qed
  next
    fix m n
    assume "m \<in> set (pg_nodes (juxtapose x y))"
      and "n \<in> set (pg_nodes (juxtapose x y))"
      and "node_name m = node_name n"
    then show "m = n"
      using assms x.node_unique_path y.node_unique_path pg_disjoint_disjoint by fastforce
  next
    fix p
    assume "p \<in> set (pg_ports (juxtapose x y))"
    then show "port.index p < length (filter (\<lambda>x. port.side x = port.side p) (pg_ports (juxtapose x y)))"
      using assms 
    proof (cases p rule: port_in_juxtapose)
      case X
      then show ?thesis
        using x.ports_index_bound by fastforce
    next
      case (Y p')
      then show ?thesis
        using y.ports_index_bound by (simp add: comp_def)
    qed
  next
    fix p q
    assume "p \<in> set (pg_ports (juxtapose x y))"
       and "q \<in> set (pg_ports (juxtapose x y))"
       and "port.side p = port.side q"
       and "port.index p = port.index q"
    note prem = this

    show "port.label p = port.label q"
      using prem(1)
    proof (cases p rule: port_in_juxtapose)
      case p: X
      show ?thesis
        using prem(2)
      proof (cases q rule: port_in_juxtapose)
        case X
        then show ?thesis
          using prem(3,4) p x.open_ports_label_eq by metis
      next
        case (Y p')
        then show ?thesis
          using prem(3,4) p x.ports_index_bound by (metis not_add_less1 shiftPort_simps(2,3))
      qed
    next
      case p: (Y p')
      show ?thesis
        using prem(2)
      proof (cases q rule: port_in_juxtapose)
        case X
        then show ?thesis
          using prem(3,4) p x.ports_index_bound by (metis not_add_less1 shiftPort_simps(2,3))
      next
        case (Y p')
        then show ?thesis
          using prem(3,4) p y.open_ports_label_eq by (metis add_left_cancel shiftPort_simps(2,3,4))
      qed
    qed
  next
    fix n p q
    assume "n \<in> set (pg_nodes (juxtapose x y))"
       and "p \<in> set (node_ports n)"
       and "q \<in> set (node_ports n)"
       and "port.side p = port.side q"
       and "port.index p = port.index q"
    then show "port.label p = port.label q"
      by (metis in_nodes_juxtaposeE x.node_ports_label_eq y.node_ports_label_eq)
  next
    show "distinct (pg_nodes (juxtapose x y))"
      using assms x.nodes_distinct y.nodes_distinct by fastforce

    have "set (pg_edges x) \<inter>
        shiftOpenInEdge (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
         (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))) `
        set (pg_edges y) =
        {}"
    proof safe
      fix e
      assume e_y: "e \<in> set (pg_edges y)"
      let ?shifted =
        " shiftOpenInEdge
            (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
            (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
            e"
      assume e_x: "?shifted \<in> set (pg_edges x)"

      have False
      proof (cases "place_open (edge_from e)")
        case True
        then obtain p
          where p_in: "p \<in> set (pg_ports x)" and p: "p = place_port (edge_from ?shifted)"
          by (metis e_x shiftOpenInEdge_simps(1) shiftOpenPlace_open(1) x.edge_from_pg x.open_port_pg)

        have "length (filter (\<lambda>x. port.side x = port.side p) (pg_ports x)) \<le> port.index p"
          using e_x by (simp add: True p)
        moreover have "port.index p < length (filter (\<lambda>x. port.side x = port.side p) (pg_ports x))"
          using p_in x.ports_index_bound by metis
        ultimately show ?thesis
          by simp
      next
        case False
        then have "edge_from e \<in> set (pgraphPlaces x)"
          using e_x x.edge_from_pg
          by (metis not_place_open shiftOpenInEdge_simps(1) shiftOpenPlace_ground(2))
        moreover have "edge_from e \<in> set (pgraphPlaces y)"
          using e_y y.edge_from_pg by simp
        ultimately show ?thesis
          using assms(3) place_in_pg_disjoint False by metis
      qed
      then show
        " shiftOpenInEdge
            (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
            (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
            e
        \<in> {}" ..
    qed
    then show "distinct (pg_edges (juxtapose x y))"
      using assms x.edges_distinct y.edges_distinct inj_shiftOpenInEdge inj_on_subset
      by (fastforce simp add: distinct_map)

    have
      " set (pg_ports x) \<inter>
        shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x))) ` set (pg_ports y)
      = {}"
      using assms x.ports_index_bound by fastforce
    then show "distinct (pg_ports (juxtapose x y))"
      using x.ports_distinct y.ports_distinct
      by (simp add: distinct_map) (metis inj_shiftPort inj_on_subset subset_UNIV)
  qed
qed

text\<open>Juxtaposition of port graphs preserves their flow\<close>
lemma port_graph_flow_juxtapose:
    fixes x y :: "('s :: side_in_out, 'a, 'p, 'l) port_graph"
  assumes "port_graph_flow x"
      and "port_graph_flow y"
      and "pg_disjoint x y"
    shows "port_graph_flow (juxtapose x y)"
proof -
  interpret x: port_graph_flow x using assms by simp
  interpret y: port_graph_flow y using assms by simp

  show ?thesis
  proof (intro port_graph_flow.intro port_graph_flow_axioms.intro)
    show "port_graph (juxtapose x y)"
      using assms port_graph_flow.axioms(1) port_graph_juxtapose by metis
  next
    fix e
    assume "e \<in> set (pg_edges (juxtapose x y))"
       and "place_open (edge_from e)"
       and "edge_in_flow e"
    then show "place_side (edge_from e) = In"
      using x.edge_from_open y.edge_from_open by fastforce
  next
    fix e
    assume "e \<in> set (pg_edges (juxtapose x y))"
       and "place_open (edge_to e)"
       and "edge_in_flow e"
    then show "place_side (edge_to e) = Out"
      using x.edge_to_open y.edge_to_open by fastforce
  next
    fix e
    assume "e \<in> set (pg_edges (juxtapose x y))"
       and "place_ground (edge_from e)"
       and "edge_in_flow e"
    then show "place_side (edge_from e) = Out"
      using x.edge_from_ground y.edge_from_ground by fastforce
  next
    fix e
    assume "e \<in> set (pg_edges (juxtapose x y))"
       and "place_ground (edge_to e)"
       and "edge_in_flow e"
    then show "place_side (edge_to e) = In"
      using x.edge_to_ground y.edge_to_ground by fastforce
  qed
qed

subsection\<open>Associativity\<close>

text\<open>
  Juxtaposition of port graphs is associative up to their equivalence assuming they are
  all port graphs with flow and none of their node names clash.
\<close>
lemma juxtapose_assoc_pgEquiv:
  fixes x y z :: "('s, 'a, 'p, 'l) port_graph"
  assumes "port_graph x"
      and "port_graph y"
      and "port_graph z"
      and "pg_disjoint x y"
      and "pg_disjoint y z"
      and "pg_disjoint x z"
      and "port_graph x'"
      and "port_graph y'"
      and "port_graph z'"
      and "pg_disjoint x' y'"
      and "pg_disjoint y' z'"
      and "pg_disjoint x' z'"
      and "x \<approx> x'"
      and "y \<approx> y'"
      and "z \<approx> z'"
    shows "juxtapose (juxtapose x y) z \<approx> juxtapose x' (juxtapose y' z')"
proof (rule pgEquivI_ex)
  interpret x: port_graph x using assms by simp
  interpret y: port_graph y using assms by simp
  interpret z: port_graph z using assms by simp
  interpret x': port_graph x' using assms by simp
  interpret y': port_graph y' using assms by simp
  interpret z': port_graph z' using assms by simp

  show "port_graph (juxtapose (juxtapose x y) z)"
    using assms pg_disjoint_juxtapose(1) port_graph_juxtapose by metis
  show "port_graph (juxtapose x' (juxtapose y' z'))"
    using assms pg_disjoint_juxtapose(2) port_graph_juxtapose by metis

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
    using assms(13) by (elim pgEquivE ; blast)
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
    using assms(14) by (elim pgEquivE ; blast)
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
    using assms(15) by (elim pgEquivE ; blast)
  note zz' = this

  show
    " set (pg_ports (juxtapose (juxtapose x y) z)) =
      set (pg_ports (juxtapose x' (juxtapose y' z')))"
    using xx'(5) yy'(5) zz'(5) pg_x pg_x' pg_y pg_y'
    by (clarsimp simp add: distinct_length_filter port_graph.ports_distinct)

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

  have
    " renameNode ?f ` set (pg_nodes (juxtapose (juxtapose x y) z)) =
      set (pg_nodes (juxtapose x' (juxtapose y' z')))"
    using renameNode_f_x xx'(1) renameNode_f_y yy'(1) renameNode_f_z zz'(1)
    by (fastforce simp add: image_Un) (* slow *)
  moreover have
    " set (pg_nodes (juxtapose (juxtapose x y) z)) =
      renameNode ?g ` set (pg_nodes (juxtapose x' (juxtapose y' z')))"
    using renameNode_g_x xx'(2) renameNode_g_y yy'(2) renameNode_g_z zz'(2)
    by (fastforce simp add: image_Un) (* slow *)
  moreover have
    " renameEdge ?f ` set (pg_edges (juxtapose (juxtapose x y) z)) =
      set (pg_edges (juxtapose x' (juxtapose y' z')))"
    using xx'(3,5) yy'(3,5) zz'(3,5)
    using renameEdge_f_x renameEdge_f_y renameEdge_f_z
    using x.ports_distinct y.ports_distinct z.ports_distinct x'.ports_distinct y'.ports_distinct z'.ports_distinct
    by (simp add: image_Un image_image distinct_length_filter del: shiftOpenInEdge_simps)
       (simp only: image_image[symmetric])
  moreover have
    " set (pg_edges (juxtapose (juxtapose x y) z)) =
      renameEdge ?g ` set (pg_edges (juxtapose x' (juxtapose y' z')))"
    using xx'(4,5) yy'(4,5) zz'(4,5)
    using renameEdge_g_x renameEdge_g_y renameEdge_g_z
    using x.ports_distinct y.ports_distinct z.ports_distinct x'.ports_distinct y'.ports_distinct z'.ports_distinct
    by (simp add: image_Un image_image distinct_length_filter del: shiftOpenInEdge_simps)
       (simp only: image_image[symmetric])
  moreover have "\<And>l. l \<in> node_name ` set (pg_nodes (juxtapose (juxtapose x y) z)) \<Longrightarrow> ?g (?f l) = l"
  proof safe
    fix n
    assume "n \<in> set (pg_nodes (juxtapose (juxtapose x y) z))"
    then consider
        (X) "n \<in> set (pg_nodes x)" and "n \<notin> set (pg_nodes y)" and "n \<notin> set (pg_nodes z)"
      | (Y) "n \<notin> set (pg_nodes x)" and "n \<in> set (pg_nodes y)" and "n \<notin> set (pg_nodes z)"
      | (Z) "n \<notin> set (pg_nodes x)" and "n \<notin> set (pg_nodes y)" and "n \<in> set (pg_nodes z)"
      using assms by (blast elim: in_nodes_juxtaposeE)
    then show "?g (?f (node_name n)) = node_name n"
    proof cases
      case X
      then show ?thesis
        using xx'(1,6) renameNode_f_x renameNode_g_x
        by (smt (z3) image_eqI renameNode_simps(2))
    next
      case Y
      then have "node_name n \<notin> node_name ` set (pg_nodes x)"
        using assms(4) by fastforce
      then show ?thesis
        using Y yy'(1,6) renameNode_f_y renameNode_g_y
        by (smt (z3) image_iff renameNode_simps(2))
    next
      case Z
      then have "node_name n \<notin> node_name ` set (pg_nodes x)"
        using assms(6) by fastforce
      moreover have "node_name n \<notin> node_name ` set (pg_nodes y)"
        using Z assms(5) by fastforce
      ultimately show ?thesis
        using Z zz'(1,6) renameNode_f_z renameNode_g_z
        by (smt (z3) image_iff renameNode_simps(2))
    qed
  qed
  moreover have "\<And>l. l \<in> node_name ` set (pg_nodes (juxtapose x' (juxtapose y' z'))) \<Longrightarrow> ?f (?g l) = l"
  proof safe
    fix n
    assume "n \<in> set (pg_nodes (juxtapose x' (juxtapose y' z')))"
    then consider
      (X) "n \<in> set (pg_nodes x')" and "n \<notin> set (pg_nodes y')" and "n \<notin> set (pg_nodes z')"
      | (Y) "n \<notin> set (pg_nodes x')" and "n \<in> set (pg_nodes y')" and "n \<notin> set (pg_nodes z')"
      | (Z) "n \<notin> set (pg_nodes x')" and "n \<notin> set (pg_nodes y')" and "n \<in> set (pg_nodes z')"
      using assms by (blast elim: in_nodes_juxtaposeE)
    then show "?f (?g (node_name n)) = node_name n"
    proof cases
      case X
      then show ?thesis
        using xx'(2,7) renameNode_f_x renameNode_g_x
        by (smt (z3) image_iff renameNode_simps(2))
    next
      case Y
      then have "node_name n \<notin> node_name ` set (pg_nodes x')"
        using assms(10) by fastforce
      then show ?thesis
        using Y yy'(2,7) renameNode_f_y renameNode_g_y
        by (smt (z3) image_iff renameNode_simps(2))
    next
      case Z
      then have "node_name n \<notin> node_name ` set (pg_nodes x')"
        using assms(12) by fastforce
      moreover have "node_name n \<notin> node_name ` set (pg_nodes y')"
        using Z assms(11) by fastforce
      ultimately show ?thesis
        using Z zz'(2,7) renameNode_f_z renameNode_g_z
        by (smt (z3) image_iff renameNode_simps(2))
    qed
  qed
  ultimately have "pgEquiv_witness ?f ?g (juxtapose (juxtapose x y) z) (juxtapose x' (juxtapose y' z'))"
    by (rule pgEquiv_witnessI)
  then show "\<exists>f g. pgEquiv_witness f g (juxtapose (juxtapose x y) z) (juxtapose x' (juxtapose y' z'))"
    by blast
qed

lemma juxtapose_assoc:
  fixes x y z :: "('s, 'a, 'p, 'l) port_graph"
  assumes "port_graph x"
      and "port_graph y"
      and "port_graph z"
      and "pg_disjoint x y"
      and "pg_disjoint y z"
      and "pg_disjoint x z"
    shows "juxtapose (juxtapose x y) z \<approx> juxtapose x (juxtapose y z)"
  using assms assms pgEquiv_refl pgEquiv_refl pgEquiv_refl
  by (rule juxtapose_assoc_pgEquiv)

subsection\<open>Qualification\<close>

text\<open>
  Qualifying a juxtaposition of port graphs is the same as juxtaposition of qualified port graphs.
\<close>
lemma qualifyPortGraph_juxtapose [simp]:
  "qualifyPortGraph a (juxtapose x y) = juxtapose (qualifyPortGraph a x) (qualifyPortGraph a y)"
  by (cases x, cases y, simp add: qualifyPortGraph_def)

subsection\<open>Respecting Equivalence\<close>

text\<open>Juxtaposition respects port graph equivalence\<close>
lemma juxtapose_resp:
  fixes x y x' y' :: "('s, 'a, 'p, 'l) port_graph"
  assumes "port_graph x"
      and "port_graph y"
      and "pg_disjoint x y"
      and "port_graph x'"
      and "port_graph y'"
      and "pg_disjoint x' y'"
      and "x \<approx> x'"
      and "y \<approx> y'"
    shows "juxtapose x y \<approx> juxtapose x' y'"
proof (rule pgEquivI_ex)
  interpret x: port_graph x using assms by simp
  interpret y: port_graph y using assms by simp
  interpret x': port_graph x' using assms by simp
  interpret y': port_graph y' using assms by simp

  show "port_graph (juxtapose x y)"
    by (metis assms(1-3) port_graph_juxtapose)
  show "port_graph (juxtapose x' y')"
    by (metis assms(4-6) port_graph_juxtapose)

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

  have len_px: "length (filter (\<lambda>x. port.side x = s) (pg_ports x)) = length (filter (\<lambda>x. port.side x = s) (pg_ports x'))" for s
    using port_graph.ports_distinct pg_x pg_x' p_xx'
    by (metis distinct_length_filter)
  then show "set (pg_ports (juxtapose x y)) = set (pg_ports (juxtapose x' y'))"
    using p_xx' p_yy' by clarsimp

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

  have "renameNode ?f ` set (pg_nodes (juxtapose x y)) = set (pg_nodes (juxtapose x' y'))"
    using renameNode_f_x xx'(1) renameNode_f_y yy'(1)
    by (fastforce simp add: image_Un)
  moreover have "set (pg_nodes (juxtapose x y)) = renameNode ?g ` set (pg_nodes (juxtapose x' y'))"
    using renameNode_g_x xx'(2) renameNode_g_y yy'(2)
    by (fastforce simp add: image_Un)
  moreover have "renameEdge ?f ` set (pg_edges (juxtapose x y)) = set (pg_edges (juxtapose x' y'))"
    using xx'(3,5) yy'(3,5)
    using renameEdge_f_x renameEdge_f_y
    using x.ports_distinct y.ports_distinct x'.ports_distinct y'.ports_distinct
    by (simp add: image_Un image_image distinct_length_filter)
       (simp only: image_image[symmetric])
  moreover have "set (pg_edges (juxtapose x y)) = renameEdge ?g ` set (pg_edges (juxtapose x' y'))"
    using xx'(4,5) yy'(4,5)
    using renameEdge_g_x renameEdge_g_y
    using x.ports_distinct y.ports_distinct x'.ports_distinct y'.ports_distinct
    by (simp add: image_Un image_image distinct_length_filter)
       (simp only: image_image[symmetric])
  moreover have "l \<in> node_name ` set (pg_nodes (juxtapose x y)) \<Longrightarrow> ?g (?f l) = l" for l
    using renameNode_f_x renameNode_f_y renameNode_g_x renameNode_g_y xx'(1,6) yy'(1,6)
    by (smt (z3) image_iff in_nodes_juxtaposeE renameNode_simps(2))
  moreover have "l \<in> node_name ` set (pg_nodes (juxtapose x' y')) \<Longrightarrow> ?f (?g l) = l" for l
    using renameNode_f_x renameNode_f_y renameNode_g_x renameNode_g_y xx'(2,7) yy'(2,7)
    by (smt (z3) image_iff in_nodes_juxtaposeE renameNode_simps(2))
  ultimately have "pgEquiv_witness ?f ?g (juxtapose x y) (juxtapose x' y')"
    by (rule pgEquiv_witnessI)
  then show "\<exists>f g. pgEquiv_witness f g (juxtapose x y) (juxtapose x' y')"
    by blast
qed

end