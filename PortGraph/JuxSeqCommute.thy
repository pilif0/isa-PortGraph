theory JuxSeqCommute
  imports
    Juxtapose
    Sequence
begin

section\<open>Commutativity of Juxtaposition and Sequencing\<close>

text\<open>
  If there were non-flow open ports in both ``middle'' two port graphs of the statement, then
  it would be differently shifted by the two forms and prevent them from being equivalent.
\<close>
(* TODO
  Maybe this is an argument to expand the equivalence, but not an urgent one as process port graphs
  will have no such ports.
 *)
lemma
  assumes "p \<in> set (pg_ports y)"
      and "q \<in> set (pg_ports u)"
      and "port.side p \<noteq> In"
      and "port.side p \<noteq> Out"
      and "port.side q = port.side p"
  obtains f g i j
    where "shiftPort f p \<in> set (pg_ports (juxtapose (seqPortGraphs x y) (seqPortGraphs u v)))"
      and "shiftPort g p \<in> set (pg_ports (seqPortGraphs (juxtapose x u) (juxtapose y v)))"
      and "f (port.side p) \<noteq> g (port.side p)"
      and "shiftPort i q \<in> set (pg_ports (juxtapose (seqPortGraphs x y) (seqPortGraphs u v)))"
      and "shiftPort j q \<in> set (pg_ports (seqPortGraphs (juxtapose x u) (juxtapose y v)))"
      and "i (port.side q) \<noteq> j (port.side q)"
proof
  let ?f = "\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))"
  let ?g = "\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x @ pg_ports u))"

  show "shiftPort ?f p \<in> set (pg_ports (juxtapose (seqPortGraphs x y) (seqPortGraphs u v)))"
    using assms(1,3,4) by simp
  show "shiftPort ?g p \<in> set (pg_ports (seqPortGraphs (juxtapose x u) (juxtapose y v)))"
    using assms(1,2,3,4) by (simp add: comp_def)
  show "?f (port.side p) \<noteq> ?g (port.side p)"
    using assms(2,5) by (fastforce simp add: filter_empty_conv)

  let ?i = "\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x @ pg_ports y))"
  let ?j = "\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x))"

  show "shiftPort ?i q \<in> set (pg_ports (juxtapose (seqPortGraphs x y) (seqPortGraphs u v)))"
    using assms(2,3,4,5)
    apply (simp add: comp_def)
    apply (rule disjI2, rule disjI2, rule disjI1)
    apply (rule image_eqI[where x = q])
    apply (cases q, simp add:)
     apply (smt (verit, best) filter_cong)
    apply simp
    done
  show "shiftPort ?j q \<in> set (pg_ports (seqPortGraphs (juxtapose x u) (juxtapose y v)))"
    using assms(2,3,4,5) by (simp add: comp_def)
  show "?i (port.side q) \<noteq> ?j (port.side q)"
    using assms(1,5) by (fastforce simp add: filter_empty_conv)
qed

(* TODO doc *)
lemma port_graph_par_seq_comm:
    fixes x y u v :: "('s :: side_in_out, 'a, 'p, 'l) port_graph"
  assumes "port_graph_flow x"
      and "port_graph_flow y"
      and "pg_disjoint x y"
      and "port_graph_flow u"
      and "port_graph_flow v"
      and "pg_disjoint u v"
      and "pg_disjoint (seqPortGraphs x y) (seqPortGraphs u v)"
      and "port_graph_flow x'"
      and "port_graph_flow u'"
      and "pg_disjoint x' u'"
      and "port_graph_flow y'"
      and "port_graph_flow v'"
      and "pg_disjoint y' v'"
      and "pg_disjoint (juxtapose x' u') (juxtapose y' v')"
      and "x \<approx> x'"
      and "y \<approx> y'"
      and "u \<approx> u'"
      and "v \<approx> v'"
      and "length (filter (\<lambda>x. port.side x = Out) (pg_ports x)) = length (filter (\<lambda>x. port.side x = In) (pg_ports y))"
      and "length (filter (\<lambda>x. port.side x = Out) (pg_ports u)) = length (filter (\<lambda>x. port.side x = In) (pg_ports v))"
      and "\<And>p. p \<in> set (pgraphPlaces x) \<Longrightarrow> place_side p = In \<or> place_side p = Out"
      and "\<And>p. p \<in> set (pgraphPlaces y) \<Longrightarrow> place_side p = In \<or> place_side p = Out"
      and "\<And>p. p \<in> set (pgraphPlaces u) \<Longrightarrow> place_side p = In \<or> place_side p = Out"
      and "\<And>p. p \<in> set (pgraphPlaces v) \<Longrightarrow> place_side p = In \<or> place_side p = Out"
(* TODO: The following assumptions get us part of the way to allowing other sides than In and Out.
         Their issues crop up with different shifting amounts, e.g. in edges from u.
      and "\<not> (\<exists>s p q. s \<noteq> In \<and> s \<noteq> Out \<and> p \<in> set (pg_ports y) \<and> q \<in> set (pg_ports u) \<and> port.side p = s \<and> port.side q = s)"
      and "\<And>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x)) = length (filter (\<lambda>x. port.side x = s) (pg_ports u))" *)
    shows "juxtapose (seqPortGraphs x y) (seqPortGraphs u v) \<approx> seqPortGraphs (juxtapose x' u') (juxtapose y' v')" (is "?parseq \<approx> ?seqpar")
proof (rule pgEquivI_ex)
  interpret x: port_graph_flow x using assms(1) .
  interpret y: port_graph_flow y using assms(2) .
  have pgf_xy: "port_graph_flow (seqPortGraphs x y)"
    using assms(1,2,3) port_graph_flow_seqPortGraphs by blast
  then interpret xy: port_graph_flow "seqPortGraphs x y" .

  interpret u: port_graph_flow u using assms(4) .
  interpret v: port_graph_flow v using assms(5) .
  have pgf_uv: "port_graph_flow (seqPortGraphs u v)"
    using assms(4,5,6) port_graph_flow_seqPortGraphs by blast
  then interpret uv: port_graph_flow "seqPortGraphs u v" .

  have pgf_xyuv: "port_graph_flow ?parseq"
    using pgf_xy pgf_uv
    apply (rule port_graph_flow_juxtapose)
    using assms(7) by (clarsimp elim: in_nodes_seqPortGraphsE)
  then interpret xyuv: port_graph_flow ?parseq .

  interpret x': port_graph_flow x' using assms(8) .
  interpret u': port_graph_flow u' using assms(9) .
  have pgf_x'u': "port_graph_flow (juxtapose x' u')"
    using assms(8,9,10) port_graph_flow_juxtapose by blast
  then interpret x'u': port_graph_flow "juxtapose x' u'" .

  interpret y': port_graph_flow y' using assms(11) .
  interpret v': port_graph_flow v' using assms(12) .
  have pgf_y'v': "port_graph_flow (juxtapose y' v')"
    using assms(11,12,13) port_graph_flow_juxtapose by blast
  then interpret y'v': port_graph_flow "juxtapose y' v'" .

  have pgf_x'u'y'v': "port_graph_flow ?seqpar"
    using pgf_x'u' pgf_y'v'
    apply (rule port_graph_flow_seqPortGraphs)
    using assms(14) by (clarsimp elim: in_nodes_juxtaposeE)
  then interpret x'u'y'v': port_graph_flow ?seqpar .

  note pg_x = x.port_graph_axioms
  note pg_y = y.port_graph_axioms
  note pg_u = u.port_graph_axioms
  note pg_v = v.port_graph_axioms
  note pg_x' = x'.port_graph_axioms
  note pg_y' = y'.port_graph_axioms
  note pg_u' = u'.port_graph_axioms
  note pg_v' = v'.port_graph_axioms

  show "port_graph ?parseq"
    using pgf_xyuv port_graph_flow.axioms by blast
  show "port_graph ?seqpar"
    using pgf_x'u'y'v' port_graph_flow.axioms by blast

  from x.port_graph_axioms x'.port_graph_axioms obtain f_x g_x
    where "renameNode f_x ` (set (pg_nodes x)) = set (pg_nodes x')"
      and "set (pg_nodes x) = renameNode g_x ` (set (pg_nodes x'))"
      and "renameEdge f_x ` (set (pg_edges x)) = set (pg_edges x')"
      and "set (pg_edges x) = renameEdge g_x ` (set (pg_edges x'))"
      and "set (pg_ports x) = set (pg_ports x')"
      and "\<And>l. l \<in> node_name ` set (pg_nodes x) \<Longrightarrow> g_x (f_x l) = l"
      and "\<And>l. l \<in> node_name ` set (pg_nodes x') \<Longrightarrow> f_x (g_x l) = l"
    using assms(15) by (elim pgEquivE ; blast)
  note xx' = this

  from y.port_graph_axioms y'.port_graph_axioms obtain f_y g_y
    where "renameNode f_y ` (set (pg_nodes y)) = set (pg_nodes y')"
      and "set (pg_nodes y) = renameNode g_y ` (set (pg_nodes y'))"
      and "renameEdge f_y ` (set (pg_edges y)) = set (pg_edges y')"
      and "set (pg_edges y) = renameEdge g_y ` (set (pg_edges y'))"
      and "set (pg_ports y) = set (pg_ports y')"
      and "\<And>l. l \<in> node_name ` set (pg_nodes y) \<Longrightarrow> g_y (f_y l) = l"
      and "\<And>l. l \<in> node_name ` set (pg_nodes y') \<Longrightarrow> f_y (g_y l) = l"
    using assms(16) by (elim pgEquivE ; blast)
  note yy' = this

  from u.port_graph_axioms u'.port_graph_axioms obtain f_u g_u
    where "renameNode f_u ` (set (pg_nodes u)) = set (pg_nodes u')"
      and "set (pg_nodes u) = renameNode g_u ` (set (pg_nodes u'))"
      and "renameEdge f_u ` (set (pg_edges u)) = set (pg_edges u')"
      and "set (pg_edges u) = renameEdge g_u ` (set (pg_edges u'))"
      and "set (pg_ports u) = set (pg_ports u')"
      and "\<And>l. l \<in> node_name ` set (pg_nodes u) \<Longrightarrow> g_u (f_u l) = l"
      and "\<And>l. l \<in> node_name ` set (pg_nodes u') \<Longrightarrow> f_u (g_u l) = l"
    using assms(17) by (elim pgEquivE ; blast)
  note uu' = this

  from v.port_graph_axioms v'.port_graph_axioms obtain f_v g_v
    where "renameNode f_v ` (set (pg_nodes v)) = set (pg_nodes v')"
      and "set (pg_nodes v) = renameNode g_v ` (set (pg_nodes v'))"
      and "renameEdge f_v ` (set (pg_edges v)) = set (pg_edges v')"
      and "set (pg_edges v) = renameEdge g_v ` (set (pg_edges v'))"
      and "set (pg_ports v) = set (pg_ports v')"
      and "\<And>l. l \<in> node_name ` set (pg_nodes v) \<Longrightarrow> g_v (f_v l) = l"
      and "\<And>l. l \<in> node_name ` set (pg_nodes v') \<Longrightarrow> f_v (g_v l) = l"
    using assms(18) by (elim pgEquivE ; blast)
  note vv' = this

  have len_fil_x: "length (filter P (pg_ports x)) = length (filter P (pg_ports x'))" for P
    using xx'(5) x.ports_distinct x'.ports_distinct
    by (metis distinct_length_filter)
  have len_fil_y: "length (filter P (pg_ports y)) = length (filter P (pg_ports y'))" for P
    using yy'(5) y.ports_distinct y'.ports_distinct
    by (metis distinct_length_filter)
  have len_fil_u: "length (filter P (pg_ports u)) = length (filter P (pg_ports u'))" for P
    using uu'(5) u.ports_distinct u'.ports_distinct
    by (metis distinct_length_filter)
  have len_fil_v: "length (filter P (pg_ports v)) = length (filter P (pg_ports v'))" for P
    using vv'(5) v.ports_distinct v'.ports_distinct
    by (metis distinct_length_filter)

  have non_flow_yu: "\<not> (\<exists>s p q. s \<noteq> In \<and> s \<noteq> Out \<and> p \<in> set (pg_ports y) \<and> q \<in> set (pg_ports u) \<and> port.side p = s \<and> port.side q = s)"
  proof safe
    fix p q
    assume "port.side p \<noteq> In" "p \<in> set (pg_ports y)"
    then have "port.side p = Out"
      using assms(22)[of "OpenPort p"] by simp
    moreover assume "port.side p \<noteq> Out" "port.side q = port.side p" "q \<in> set (pg_ports u)"
    then have "port.side q = In"
      using assms(23)[of "OpenPort q"] by simp
    ultimately have "port.side p \<noteq> port.side q"
      by (metis in_out_distinct)
    moreover assume "port.side q = port.side p"
    ultimately show False
      by metis
  qed
  then have non_flow_y'u': "\<not> (\<exists>s p q. s \<noteq> In \<and> s \<noteq> Out \<and> p \<in> set (pg_ports y') \<and> q \<in> set (pg_ports u') \<and> port.side p = s \<and> port.side q = s)"
    using yy'(5) uu'(5) by metis

  show "set (pg_ports ?parseq) = set (pg_ports ?seqpar)"
  proof safe
    fix p
    assume "p \<in> set (pg_ports ?parseq)"
    moreover have
      " shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x'))) p
      \<in> shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x')) +
                       length (filter (\<lambda>x. port.side x = s) (pg_ports u'))) `
            {x \<in> set (pg_ports y'). port.side x \<noteq> In \<and> port.side x \<noteq> Out}"
      if "p \<in> set (pg_ports y')" and "port.side p \<noteq> In" and "port.side p \<noteq> Out" for p
    proof (rule image_eqI)
      show "p \<in> {x \<in> set (pg_ports y'). port.side x \<noteq> In \<and> port.side x \<noteq> Out}"
        using that by simp
      show
        " shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x'))) p
        = shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x')) +
                         length (filter (\<lambda>x. port.side x = s) (pg_ports u'))) p"
        using that non_flow_y'u' shiftPort_def
        by (smt (verit) add.right_neutral filter_False list.size(3) shiftPort_simps(2))
    qed
    moreover have
      " shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = s) (pg_ports x')) +
                        (length (filter (\<lambda>x. port.side x = Out \<and> port.side x = s) (pg_ports y')) +
                          length (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = s) (pg_ports y'))))
        p \<in> shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x'))) ` set (pg_ports u')"
      if "p \<in> set (pg_ports u')" and "port.side p \<noteq> Out" for p
    proof (rule image_eqI)
      show "p \<in> set (pg_ports u')" using that(1) .
      show
        " shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = s) (pg_ports x')) +
                          (length (filter (\<lambda>x. port.side x = Out \<and> port.side x = s) (pg_ports y')) +
                            length (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = s) (pg_ports y'))))
          p = shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x'))) p"
      proof (cases "port.side p = In")
        case True
        then show ?thesis
          using shiftPort_def that(2)
          by (smt (verit, best) add.commute add_cancel_left_left filter_False filter_cong list.size(3))
      next
        case False
        then show ?thesis
          using non_flow_y'u' that shiftPort_def
          by (smt (verit, best) add.commute add_cancel_left_left filter_False filter_cong length_0_conv)
      qed
    qed
    moreover have
      " shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = s) (pg_ports x')) +
                        (length (filter (\<lambda>x. port.side x = Out \<and> port.side x = s) (pg_ports y')) +
                          length (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = s) (pg_ports y'))))
        p \<in> shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports y'))) ` set (pg_ports v')"
      if "p \<in> set (pg_ports v')" and "port.side p = Out" for p
    proof (rule image_eqI)
      show "p \<in> set (pg_ports v')" using that(1) .
      show
        " shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = s) (pg_ports x')) +
                          (length (filter (\<lambda>x. port.side x = Out \<and> port.side x = s) (pg_ports y')) +
                            length (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = s) (pg_ports y'))))
          p = shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports y'))) p"
        using that(2) by (simp add: shiftPort_def)
    qed
    moreover have
      " shiftPort
              (\<lambda>s. length (filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = s) (pg_ports x')) +
                   (length (filter (\<lambda>x. port.side x = Out \<and> port.side x = s) (pg_ports y')) +
                    length (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = s) (pg_ports y'))) +
                   length (filter (\<lambda>p. port.side p = s) (pg_ports u')))
              p
             \<in> shiftPort
                 (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x')) +
                      length (filter (\<lambda>x. port.side x = s) (pg_ports u'))) `
                {x \<in> shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports y'))) ` set (pg_ports v').
                 port.side x \<noteq> In \<and> port.side x \<noteq> Out}"
      if "p \<in> set (pg_ports v')" and "port.side p \<noteq> In" and "port.side p \<noteq> Out" for p
    proof (rule image_eqI)
      show
        " shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports y'))) p
        \<in> {x \<in> shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports y'))) ` set (pg_ports v'). port.side x \<noteq> In \<and> port.side x \<noteq> Out}"
        using that by simp
      show
        " shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = s) (pg_ports x')) +
                          (length (filter (\<lambda>x. port.side x = Out \<and> port.side x = s) (pg_ports y')) +
                            length (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = s) (pg_ports y'))) +
                          length (filter (\<lambda>p. port.side p = s) (pg_ports u'))) p
        = shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x')) + length (filter (\<lambda>x. port.side x = s) (pg_ports u')))
            (shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports y'))) p)"
        using that by (simp add: shiftPort_def) (smt (verit) filter_cong)
    qed
    ultimately show "p \<in> set (pg_ports ?seqpar)"
      apply (simp add: xx'(5) yy'(5) uu'(5) vv'(5) len_fil_x len_fil_y len_fil_u len_fil_v comp_def)
      apply (elim disjE imageE CollectE conjE)
           apply blast
          apply blast
         apply blast
        apply (metis (no_types, lifting) shiftPort_simps(2))
       apply (metis (no_types, lifting) shiftPort_simps(2))
      apply (metis (no_types, lifting))
      done
  next
    fix p
    assume "p \<in> set (pg_ports ?seqpar)"
    moreover have
      " shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x'))) p
      \<in> shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = s) (pg_ports x')) +
                        (length (filter (\<lambda>x. port.side x = Out \<and> port.side x = s) (pg_ports y')) +
                          length (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = s) (pg_ports y')))) `
          {x \<in> set (pg_ports u'). port.side x \<noteq> Out}"
      if "p \<in> set (pg_ports u')" and "port.side p \<noteq> Out" for p
    proof (rule image_eqI)
      show "p \<in> {x \<in> set (pg_ports u'). port.side x \<noteq> Out}"
        using that by simp
      show
        " shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x'))) p
        = shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = s) (pg_ports x')) +
                          (length (filter (\<lambda>x. port.side x = Out \<and> port.side x = s) (pg_ports y')) +
                            length (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = s) (pg_ports y')))) p"
        using that non_flow_y'u'
        by (simp add: shiftPort_def)
           (smt (verit, ccfv_threshold) add_cancel_right_right filter_False filter_cong length_0_conv)
    qed
    moreover have
      " shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports y'))) p
      \<in> shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = s) (pg_ports x')) +
                        (length (filter (\<lambda>x. port.side x = Out \<and> port.side x = s) (pg_ports y')) +
                          length (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = s) (pg_ports y')))) `
          {x \<in> set (pg_ports v'). port.side x = Out}"
      if "p \<in> set (pg_ports v')" and "port.side p = Out" for p
    proof
      show "p \<in> {x \<in> set (pg_ports v'). port.side x = Out}"
        using that by simp
      show
        " shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports y'))) p
        = shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = s) (pg_ports x')) +
                          (length (filter (\<lambda>x. port.side x = Out \<and> port.side x = s) (pg_ports y')) +
                            length (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = s) (pg_ports y')))) p"
        using that by (simp add: shiftPort_def)
    qed
    moreover have
      " shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x')) +
                       length (filter (\<lambda>x. port.side x = s) (pg_ports u'))) p
      \<in> shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x'))) `
          {x \<in> set (pg_ports y'). port.side x \<noteq> In \<and> port.side x \<noteq> Out}"
      if "p \<in> set (pg_ports y')" and "port.side p \<noteq> In" and "port.side p \<noteq> Out" for p
    proof (rule image_eqI)
      show "p \<in> {x \<in> set (pg_ports y'). port.side x \<noteq> In \<and> port.side x \<noteq> Out}"
        using that by simp
      show
        " shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x')) + length (filter (\<lambda>x. port.side x = s) (pg_ports u'))) p
        = shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x'))) p"
        using that
        by (simp add: shiftPort_def)
           (meson non_flow_y'u' filter_False)
    qed
    moreover have
      " shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x')) +
                       length (filter (\<lambda>x. port.side x = s) (pg_ports u')) +
                       length (filter (\<lambda>p. port.side p = s) (pg_ports y'))) p
      \<in> shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = s) (pg_ports x')) +
                       (length (filter (\<lambda>x. port.side x = Out \<and> port.side x = s) (pg_ports y')) +
                        length (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = s) (pg_ports y'))) +
                       length (filter (\<lambda>p. port.side p = s) (pg_ports u'))) `
          {x \<in> set (pg_ports v'). port.side x \<noteq> In \<and> port.side x \<noteq> Out}"
      if "p \<in> set (pg_ports v')" and "port.side p \<noteq> In" and "port.side p \<noteq> Out" for p
    proof (rule image_eqI)
      show "p \<in> {x \<in> set (pg_ports v'). port.side x \<noteq> In \<and> port.side x \<noteq> Out}"
        using that by simp
      show
        " shiftPort (\<lambda>s. length (filter (\<lambda>p. port.side p = s) (pg_ports x')) +
                         length (filter (\<lambda>x. port.side x = s) (pg_ports u')) +
                         length (filter (\<lambda>p. port.side p = s) (pg_ports y'))) p
        = shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x \<noteq> Out \<and> port.side x = s) (pg_ports x')) +
                         (length (filter (\<lambda>x. port.side x = Out \<and> port.side x = s) (pg_ports y')) +
                          length (filter (\<lambda>x. port.side x \<noteq> In \<and> port.side x \<noteq> Out \<and> port.side x = s) (pg_ports y'))) +
                         length (filter (\<lambda>p. port.side p = s) (pg_ports u'))) p"
        using that
        by (simp add: shiftPort_def)
           (smt (verit, del_insts) filter_cong)
    qed
    ultimately show "p \<in> set (pg_ports ?parseq)"
      apply (simp add: xx'(5) yy'(5) uu'(5) vv'(5) len_fil_x len_fil_y len_fil_u len_fil_v comp_def)
      apply (elim disjE imageE CollectE conjE)
           apply blast
          apply (metis (no_types, lifting) shiftPort_simps(2))
         apply blast
        apply (metis (no_types, lifting) shiftPort_simps(2))
       apply blast
      apply (hypsubst, unfold shiftPort_twice shiftPort_simps(2), blast)
      done
  qed

  let ?f = "\<lambda>p.
    if p \<in> set (map node_name (pg_nodes x))
      then f_x p
      else if p \<in> set (map node_name (pg_nodes y))
        then f_y p
        else if p \<in> set (map node_name (pg_nodes u))
          then f_u p
          else if p \<in> set (map node_name (pg_nodes v))
            then f_v p
            else undefined"

  (* TODO I wish there was a command to assign a list of theorems in sequence to a list of names *)
  have pg_disjoints:
    "pg_disjoint x y" "pg_disjoint x u" "pg_disjoint x v" "pg_disjoint y u" "pg_disjoint y v" "pg_disjoint u v"
    using assms(3,6,7) by (simp_all del: seqPortGraphs.simps juxtapose.simps)
  note thm_buffer = pgEquiv_witness_combine_4[OF pg_x pg_y pg_u pg_v pg_disjoints, where f_x = f_x and f_y = f_y and f_u = f_u and f_v = f_v]
  note renameNode_f_x = thm_buffer(1)
  note renameNode_f_y = thm_buffer(2)
  note renameNode_f_u = thm_buffer(3)
  note renameNode_f_v = thm_buffer(4)
  note renamePlace_f_x = thm_buffer(5)
  note renamePlace_f_y = thm_buffer(6)
  note renamePlace_f_u = thm_buffer(7)
  note renamePlace_f_v = thm_buffer(8)
  note renameEdge_f_x = thm_buffer(9)
  note renameEdge_f_y = thm_buffer(10)
  note renameEdge_f_u = thm_buffer(11)
  note renameEdge_f_v = thm_buffer(12)

  let ?g = "\<lambda>p.
    if p \<in> set (map node_name (pg_nodes x'))
      then g_x p
      else if p \<in> set (map node_name (pg_nodes y'))
        then g_y p
        else if p \<in> set (map node_name (pg_nodes u'))
          then g_u p
          else if p \<in> set (map node_name (pg_nodes v'))
            then g_v p
            else undefined"

  (* TODO I wish there was a command to assign a list of theorems in sequence to a list of names *)
  have pg_disjoints':
    "pg_disjoint x' y'" "pg_disjoint x' u'" "pg_disjoint x' v'" "pg_disjoint y' u'" "pg_disjoint y' v'" "pg_disjoint u' v'"
    using assms(10,13,14) by (simp_all del: seqPortGraphs.simps juxtapose.simps add: sym_pg_disjoint)
  note thm_buffer = pgEquiv_witness_combine_4[OF pg_x' pg_y' pg_u' pg_v' pg_disjoints', where f_x = g_x and f_y = g_y and f_u = g_u and f_v = g_v]
  note renameNode_g_x = thm_buffer(1)
  note renameNode_g_y = thm_buffer(2)
  note renameNode_g_u = thm_buffer(3)
  note renameNode_g_v = thm_buffer(4)
  note renamePlace_g_x = thm_buffer(5)
  note renamePlace_g_y = thm_buffer(6)
  note renamePlace_g_u = thm_buffer(7)
  note renamePlace_g_v = thm_buffer(8)
  note renameEdge_g_x = thm_buffer(9)
  note renameEdge_g_y = thm_buffer(10)
  note renameEdge_g_u = thm_buffer(11)
  note renameEdge_g_v = thm_buffer(12)

  have inv_on_places_x:
    "p \<in> set (pgraphPlaces x) \<Longrightarrow> renamePlace ?g (renamePlace ?f p) = p" for p
    apply (simp, elim disjE; clarsimp)
    using xx'(1,6) apply clarsimp
    by (metis image_iff renameNode_simps(2))
  then have inv_on_edges_x:
    "e \<in> set (pg_edges x) \<Longrightarrow> renameEdge ?g (renameEdge ?f e) = e" for e
    by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3) x.edge_from_pg x.edge_to_pg)

  have inv_on_places_x':
    "p \<in> set (pgraphPlaces x') \<Longrightarrow> renamePlace ?f (renamePlace ?g p) = p" for p
    apply (simp, elim disjE; clarsimp)
    using xx'(2,7) apply clarsimp
    by (metis image_iff renameNode_simps(2))
  then have inv_on_edges_x':
    "e \<in> set (pg_edges x') \<Longrightarrow> renameEdge ?f (renameEdge ?g e) = e" for e
    by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3) x'.edge_from_pg x'.edge_to_pg)

  have inv_on_places_y:
    "renamePlace ?g (renamePlace ?f p) = p" if p: "p \<in> set (pgraphPlaces y)" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes y)" and "node_name n \<notin> node_name ` set (pg_nodes x)"
      using p pg_disjoints True
      by (metis pg_disjoint_setD nodePlacesE pgraphPlaces_ground sym_pg_disjoint)
    ultimately show ?thesis
      using renameNode_g_y yy'(1,6)
      by simp (smt (z3) image_iff renameNode_simps(2))
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed
  then have inv_on_edges_y:
    "e \<in> set (pg_edges y) \<Longrightarrow> renameEdge ?g (renameEdge ?f e) = e" for e
    by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3) y.edge_from_pg y.edge_to_pg)

  have inv_on_places_y':
    "renamePlace ?f (renamePlace ?g p) = p" if p: "p \<in> set (pgraphPlaces y')" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes y')" and "node_name n \<notin> node_name ` set (pg_nodes x')"
      using p pg_disjoints' True
      by (metis pg_disjoint_setD nodePlacesE pgraphPlaces_ground sym_pg_disjoint)
    ultimately show ?thesis
      using renameNode_f_y yy'(2,7)
      by simp (smt (z3) image_iff renameNode_simps(2))
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed
  then have inv_on_edges_y':
    "e \<in> set (pg_edges y') \<Longrightarrow> renameEdge ?f (renameEdge ?g e) = e" for e
    by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3) y'.edge_from_pg y'.edge_to_pg)

  have inv_on_places_u:
    "renamePlace ?g (renamePlace ?f p) = p" if p: "p \<in> set (pgraphPlaces u)" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes u)" and "node_name n \<notin> node_name ` set (pg_nodes x)"
        and "node_name n \<notin> node_name ` set (pg_nodes y)"
      using p pg_disjoints True
      by (metis pg_disjoint_setD nodePlacesE pgraphPlaces_ground sym_pg_disjoint)
    ultimately show ?thesis
      using renameNode_g_u uu'(1,6)
      by simp (smt (verit) imageI list.set_map renameNode_simps(2))
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed
  then have inv_on_edges_u:
    "e \<in> set (pg_edges u) \<Longrightarrow> renameEdge ?g (renameEdge ?f e) = e" for e
    by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3) u.edge_from_pg u.edge_to_pg)

  have inv_on_places_u':
    "renamePlace ?f (renamePlace ?g p) = p" if p: "p \<in> set (pgraphPlaces u')" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes u')" and "node_name n \<notin> node_name ` set (pg_nodes x')"
        and "node_name n \<notin> node_name ` set (pg_nodes y')"
      using p pg_disjoints' True
      by (metis pg_disjoint_setD nodePlacesE pgraphPlaces_ground sym_pg_disjoint)
    ultimately show ?thesis
      using renameNode_f_u uu'(2,7)
      by simp (smt (verit) imageI list.set_map renameNode_simps(2))
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed
  then have inv_on_edges_u':
    "e \<in> set (pg_edges u') \<Longrightarrow> renameEdge ?f (renameEdge ?g e) = e" for e
    by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3) u'.edge_from_pg u'.edge_to_pg)

  have inv_on_places_v:
    "renamePlace ?g (renamePlace ?f p) = p" if p: "p \<in> set (pgraphPlaces v)" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes v)" and "node_name n \<notin> node_name ` set (pg_nodes x)"
        and "node_name n \<notin> node_name ` set (pg_nodes y)"
        and "node_name n \<notin> node_name ` set (pg_nodes u)"
      using p pg_disjoints True
      by (metis pg_disjoint_setD nodePlacesE pgraphPlaces_ground sym_pg_disjoint)
    ultimately show ?thesis
      using renameNode_g_v vv'(1,6)
      by simp (smt (verit) imageI list.set_map renameNode_simps(2))
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed
  then have inv_on_edges_v:
    "e \<in> set (pg_edges v) \<Longrightarrow> renameEdge ?g (renameEdge ?f e) = e" for e
    by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3) v.edge_from_pg v.edge_to_pg)

  have inv_on_places_v':
    "renamePlace ?f (renamePlace ?g p) = p" if p: "p \<in> set (pgraphPlaces v')" for p
  proof (cases "place_ground p")
    case True
    moreover obtain n qp port
      where "p = GroundPort qp" and "qp = QPort port (node_name n)"
        and "n \<in> set (pg_nodes v')" and "node_name n \<notin> node_name ` set (pg_nodes x')"
        and "node_name n \<notin> node_name ` set (pg_nodes y')"
        and "node_name n \<notin> node_name ` set (pg_nodes u')"
      using p pg_disjoints' True
      by (metis pg_disjoint_setD nodePlacesE pgraphPlaces_ground sym_pg_disjoint)
    ultimately show ?thesis
      using renameNode_f_v vv'(2,7)
      by simp (smt (verit) imageI list.set_map renameNode_simps(2))
  next
    case False
    then show ?thesis by (simp add: not_place_ground)
  qed
  then have inv_on_edges_v':
    "e \<in> set (pg_edges v') \<Longrightarrow> renameEdge ?f (renameEdge ?g e) = e" for e
    by (metis (no_types, lifting) edge.expand renameEdge_simps(2) renameEdge_simps(3) v'.edge_from_pg v'.edge_to_pg)

  have len_ports_xx': "length (filter (\<lambda>x. port.side x = s) (pg_ports x)) = length (filter (\<lambda>x. port.side x = s) (pg_ports x'))" for s
    using xx'(5) by (simp add: distinct_length_filter x'.ports_distinct x.ports_distinct)
  have len_ports_yy': "length (filter (\<lambda>x. port.side x = s) (pg_ports y)) = length (filter (\<lambda>x. port.side x = s) (pg_ports y'))" for s
    using yy'(5) by (simp add: distinct_length_filter y'.ports_distinct y.ports_distinct)
  have len_ports_uu': "length (filter (\<lambda>x. port.side x = s) (pg_ports u)) = length (filter (\<lambda>x. port.side x = s) (pg_ports u'))" for s
    using uu'(5) by (simp add: distinct_length_filter u'.ports_distinct u.ports_distinct)
  have len_ports_vv': "length (filter (\<lambda>x. port.side x = s) (pg_ports v)) = length (filter (\<lambda>x. port.side x = s) (pg_ports v'))" for s
    using vv'(5) by (simp add: distinct_length_filter v'.ports_distinct v.ports_distinct)

  have len_xy: "length (filter (\<lambda>x. port.side x = Out) (pg_ports x)) = length (filter (\<lambda>x. port.side x = In) (pg_ports y))"
    using assms(19) .
  then have len_x'y': "length (filter (\<lambda>x. port.side x = Out) (pg_ports x')) = length (filter (\<lambda>x. port.side x = In) (pg_ports y'))"
    using len_ports_xx' len_ports_yy' by simp
  have len_uv: "length (filter (\<lambda>x. port.side x = Out) (pg_ports u)) = length (filter (\<lambda>x. port.side x = In) (pg_ports v))"
    using assms(20) .
  then have len_u'v': "length (filter (\<lambda>x. port.side x = Out) (pg_ports u')) = length (filter (\<lambda>x. port.side x = In) (pg_ports v'))"
    using len_ports_uu' len_ports_vv' by simp

  have shiftOpenPlace_eqD:
    "shiftOpenPlace n p = OpenPort (Port s (n s + i) l) \<Longrightarrow> p = OpenPort (Port s i l)" for n p s i l
    by (metis add_diff_cancel_left' place_open_def place_port.simps(2) port.exhaust_sel port.inject
        shiftOpenPlace_open(1) shiftOpenPlace_open(2) shiftPort_def)

  have sides_v': "place_side p = In \<or> place_side p = Out" if p: "p \<in> set (pgraphPlaces v')" for p
    (* TODO extract general property of equivalent port graphs *)
  proof (cases p)
    case (GroundPort qp)
    then obtain n where "n \<in> set (pg_nodes v')" and "p \<in> set (nodePlaces n)"
      using p by fastforce
    then have "renameNode g_v n \<in> set (pg_nodes v)"
          and "renamePlace g_v p \<in> set (nodePlaces (renameNode g_v n))"
      using vv'(2) by fastforce+
    then have "renamePlace g_v p \<in> set (pgraphPlaces v)"
      by fastforce
    then have "place_side (renamePlace g_v p) = In \<or> place_side (renamePlace g_v p) = Out"
      using assms(24) by metis
    then show ?thesis
      by simp
  next
    case (OpenPort p')
    then have "p' \<in> set (pg_ports v')"
      using p by fastforce
    then have "p' \<in> set (pg_ports v)"
      using vv'(5) by metis
    then have "p \<in> set (pgraphPlaces v)"
      using OpenPort by simp
    then show ?thesis
      using assms(24) by metis
  qed

  have "renameNode ?f ` set (pg_nodes ?parseq) = set (pg_nodes ?seqpar)"
    unfolding seqPortGraphs.simps juxtapose.simps port_graph.sel set_append image_Un
    using renameNode_f_x xx'(1) renameNode_f_y yy'(1) renameNode_f_u uu'(1) renameNode_f_v vv'(1)
    by auto
  moreover have "set (pg_nodes ?parseq) = renameNode ?g ` set (pg_nodes ?seqpar)"
    unfolding seqPortGraphs.simps juxtapose.simps port_graph.sel set_append image_Un
    using renameNode_g_x xx'(2) renameNode_g_y yy'(2) renameNode_g_u uu'(2) renameNode_g_v vv'(2)
    by auto
  moreover have "renameEdge ?f ` set (pg_edges ?parseq) = set (pg_edges ?seqpar)"
            and "set (pg_edges ?parseq) = renameEdge ?g ` set (pg_edges ?seqpar)"
  proof -
    let ?shiftSeqX = "(\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))"
    let ?shiftSeqU = "(\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports u)))"
    let ?shiftXY = "(\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (seqPortGraphs x y))))"

    let ?shiftX'Y' = "(\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (seqPortGraphs x' y'))))"
    let ?shiftX' = "(\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x')))"
    let ?shiftY' = "(\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports y')))"

    let ?shiftSeqX'U' = "(\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports (juxtapose x' u'))))"

    have decompose_seqPar_interface:
      " set (seqInterfaceEdges (juxtapose x' u') (juxtapose y' v'))
      = set (seqInterfaceEdges x' y') \<union> shiftOpenInEdge ?shiftX' ?shiftY' ` set (seqInterfaceEdges u' v')"
      \<comment> \<open>Prove interface in seq-of-par pattern can be split into two interfaces by proving three inclusions\<close>
    proof (intro set_eqI iffI ; elim seqInterfaceEdges_setD UnE imageE)
      fix e a b and p :: "('s, 'a) port"
      assume  "edge_from e = edge_from a" and "a \<in> set (pg_edges (juxtapose x' u'))"
          and "edge_to e = edge_to b" and "b \<in> set (pg_edges (juxtapose y' v'))"
          and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
          and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
          and "port.side p = Out"
      note abp = this

      consider "a \<in> set (pg_edges x')" and "b \<in> set (pg_edges y')"
        | "a \<in> set (pg_edges x')" and "b \<in> shiftOpenInEdge ?shiftY' ?shiftY' ` set (pg_edges v')"
        | "a \<in> shiftOpenInEdge ?shiftX' ?shiftX' ` set (pg_edges u')" and "b \<in> set (pg_edges y')"
        | "a \<in> shiftOpenInEdge ?shiftX' ?shiftX' ` set (pg_edges u')" and "b \<in> shiftOpenInEdge ?shiftY' ?shiftY' ` set (pg_edges v')"
        using abp(2,4) by simp blast
      then consider
          (XY) "a \<in> set (pg_edges x')" and "b \<in> set (pg_edges y')"
        | (UV) "a \<in> shiftOpenInEdge ?shiftX' ?shiftX' ` set (pg_edges u')" and "b \<in> shiftOpenInEdge ?shiftY' ?shiftY' ` set (pg_edges v')"
          \<comment> \<open>There is no crossover, so the middle two above cases are contradictions, shown by interface port index\<close>
      proof cases
        case 1 then show ?thesis using that(1) by metis
      next
        case 2

        have "port.index p < length (filter (\<lambda>x. port.side x = Out) (pg_ports x'))"
          using 2(1) abp(5) x'.ports_index_bound x'.open_port_pg x'.edge_to_pg
          by (metis abp(9) place.disc(4) place_port.simps(2) portSetSide_same)
        moreover have "port.index p \<ge> length (filter (\<lambda>x. port.side x = Out) (pg_ports x'))"
        proof -
          have "place_open (edge_from b)" and "place_side (edge_from b) = In"
            using abp(7) by simp_all
          then have "port.index (place_port (edge_from b)) \<ge> length (filter (\<lambda>x. port.side x = Out) (pg_ports x'))"
            using 2(2) len_x'y' by clarsimp
          moreover have "port.index p = port.index (place_port (edge_from b))"
            using abp(7) by simp
          ultimately show ?thesis
            by metis
        qed
        ultimately show ?thesis by simp
      next
        case 3

        have "port.index p < length (filter (\<lambda>x. port.side x = In) (pg_ports y'))"
          using 3(2) abp(7) y'.ports_index_bound y'.open_port_pg y'.edge_from_pg
          by (metis place.disc(4) place_port.simps(2) portSetSide_index portSetSide_side)
        moreover have "port.index p \<ge> length (filter (\<lambda>x. port.side x = In) (pg_ports y'))"
        proof -
          have "place_open (edge_to a)" and "place_side (edge_to a) = Out"
            using abp(5) by simp_all
          then have "port.index (place_port (edge_to a)) \<ge> length (filter (\<lambda>x. port.side x = In) (pg_ports y'))"
            using 3(1) len_x'y' by clarsimp
          moreover have "port.index p = port.index (place_port (edge_to a))"
            using abp(5) by simp
          ultimately show ?thesis
            by metis
        qed
        ultimately show ?thesis by simp
      next case 4 then show ?thesis using that(2) by metis
      qed
      then show "e \<in>
        set (seqInterfaceEdges x' y') \<union>
        shiftOpenInEdge (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports x')))
                           (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports y')))
          ` set (seqInterfaceEdges u' v')"
        \<comment> \<open>First case is simple, in the second we make the connection with unshifted edges and then shift the result\<close>
      proof cases
        case XY
        then show ?thesis
          using assms(8,11) abp(1,3,5,7) by (metis UnI1 seqInterfaceEdges_setI)
      next
        case UV

        obtain a' where a': "a = shiftOpenInEdge ?shiftX' ?shiftX' a'" "a' \<in> set (pg_edges u')"
          using UV(1) by blast
        obtain b' where b': "b = shiftOpenInEdge ?shiftY' ?shiftY' b'" "b' \<in> set (pg_edges v')"
          using UV(2) by blast
        obtain p' where p': "p = shiftPort ?shiftX' p'"
          using a'(1) abp(5,9)
          by (metis place.disc(4) place_port.simps(2) portSetSide_same shiftOpenInEdge_simps(2) shiftOpenPlace_open)

        have "e = shiftOpenInEdge ?shiftX' ?shiftY' (Edge (edge_from a') (edge_to b'))"
          using a'(1) b'(1) abp(1,3)
          by (metis edge.collapse edge.sel shiftOpenInEdge_simps)
        moreover have "Edge (edge_from a') (edge_to b') \<in> set (seqInterfaceEdges u' v')"
          using assms(9,12)
        proof (rule seqInterfaceEdges_setI)
          show "edge_from (Edge (edge_from a') (edge_to b')) = edge_from a'" by simp
          show "a' \<in> set (pg_edges u')" using a'(2) .
          show "edge_to (Edge (edge_from a') (edge_to b')) = edge_to b'" by simp
          show "b' \<in> set (pg_edges v')" using b'(2) .
          show "edge_to a' = OpenPort (portSetSide Out p')"
            using a'(1) abp(5,9) p'
            by (simp add: shiftPort_def)
               (metis port.collapse shiftOpenPlace_eqD)
          show "edge_from b' = OpenPort (portSetSide In p')"
            using b'(1) abp(7,9) p'
            by (simp add: shiftPort_def len_x'y')
               (metis port.collapse portSetSide_index portSetSide_label portSetSide_side shiftOpenPlace_eqD)
        qed
        ultimately show ?thesis by blast
      qed
    next
      fix e a b and p :: "('s, 'a) port"
      assume  "edge_from e = edge_from a" and "a \<in> set (pg_edges x')"
          and "edge_to e = edge_to b" and "b \<in> set (pg_edges y')"
          and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
          and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
          and "port.side p = Out"
      note abp = this
      then show "e \<in> set (seqInterfaceEdges (juxtapose x' u') (juxtapose y' v'))"
        \<comment> \<open>Starting with interfacing edges in @{term x'} and @{term y'} is the simple case\<close>
        using pgf_x'u' pgf_y'v'
        by (metis UnCI juxtapose.simps port_graph.sel(2) seqInterfaceEdges_setI set_append)
    next
      fix e e' :: "('s, 'a, 'p) edge"
      assume e: "e = shiftOpenInEdge ?shiftX' ?shiftY' e'"
      fix a b and p :: "('s, 'a) port"
      assume  "edge_from e' = edge_from a" and "a \<in> set (pg_edges u')"
          and "edge_to e' = edge_to b" and "b \<in> set (pg_edges v')"
          and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
          and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
          and "port.side p = Out"
      note abp = this

      show "e \<in> set (seqInterfaceEdges (juxtapose x' u') (juxtapose y' v'))"
        \<comment> \<open>Starting with edges in @{term u'} and @{term v'} interfacing to an unshifted edge means
            that we need to shift them and interface the results\<close>
        using pgf_x'u' pgf_y'v'
      proof (rule seqInterfaceEdges_setI)
        show "edge_from e = edge_from (shiftOpenInEdge ?shiftX' ?shiftX' a)"
          by (simp add: abp(1) e)
        show "shiftOpenInEdge ?shiftX' ?shiftX' a \<in> set (pg_edges (juxtapose x' u'))"
          using abp(2) by force
        show "edge_to e = edge_to (shiftOpenInEdge ?shiftY' ?shiftY' b)"
          by (simp add: abp(3) e)
        show "shiftOpenInEdge ?shiftY' ?shiftY' b \<in> set (pg_edges (juxtapose y' v'))"
          using abp(4) by force
        show "edge_to (shiftOpenInEdge ?shiftX' ?shiftX' a) = OpenPort (portSetSide Out (shiftPort ?shiftX' p))"
          by (simp add: abp(5,9))
        show "edge_from (shiftOpenInEdge ?shiftY' ?shiftY' b) = OpenPort (portSetSide In (shiftPort ?shiftX' p))"
          using abp(7,9) by (simp add: shiftPort_def len_x'y')
      qed
    qed

    
    show "renameEdge ?f ` set (pg_edges ?parseq) = set (pg_edges ?seqpar)"
     and "set (pg_edges ?parseq) = renameEdge ?g ` set (pg_edges ?seqpar)"
    proof safe
      fix e
      assume "e \<in> set (pg_edges ?parseq)"
      then consider
        "e \<in> set (pg_edges (seqPortGraphs x y))"
        | "e \<in> shiftOpenInEdge ?shiftXY ?shiftXY ` set (pg_edges (seqPortGraphs u v))"
        unfolding juxtapose.simps port_graph.sel set_append set_map
        by blast
      then consider
            (XY) "e \<in> set (seqInterfaceEdges x y)"
          | (X)  "e \<in> set (pg_edges x)" and "\<not> toOpenOut e"
          | (Y)  e' where "e' \<in> set (pg_edges y)" and "\<not> fromOpenIn e'" and "e = shiftOpenInEdge ?shiftSeqX ?shiftSeqX e'"
          | (UV) e' where "e = shiftOpenInEdge ?shiftXY ?shiftXY e'" and "e' \<in> set (seqInterfaceEdges u v)"
          | (U)  e' where "e = shiftOpenInEdge ?shiftXY ?shiftXY e'" and "e' \<in> set (pg_edges u)" and "\<not> toOpenOut e'"
          | (V)  e' where "e' \<in> set (pg_edges v)" and "\<not> fromOpenIn e'" and "e = shiftOpenInEdge ?shiftXY ?shiftXY (shiftOpenInEdge ?shiftSeqX ?shiftSeqX e')"
          \<comment> \<open>Edge being considered is either fully in one constituent port graph or one of the two interfaces\<close>
      proof cases
        case 1
        show ?thesis
           using assms(1,2) 1
        proof (cases rule: seqPortGraphs_edge_cases)
             case Stitch then show ?thesis using that(1) by blast
        next case L then show ?thesis using that(2) by blast
        next case (R e') then show ?thesis using that(3) by blast
        qed
      next
        case 2
        then obtain e'
          where "e = shiftOpenInEdge ?shiftXY ?shiftXY e'" and "e' \<in> set (pg_edges (seqPortGraphs u v))"
          by blast
        note e' = this
  
        show ?thesis
           using assms(4,5) e'(2)
        proof (cases rule: seqPortGraphs_edge_cases)
             case Stitch then show ?thesis using e' that(4) by blast
        next case L then show ?thesis using e' that(5) by blast
        next
          case (R e'')
          moreover have "e =
            shiftOpenInEdge (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (seqPortGraphs x y))))
                               (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (seqPortGraphs x y))))
            ( shiftOpenInEdge (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
                                 (\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x)))
              e'')"
          proof -
            have u: "(\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports u))) = (\<lambda>s. 0)"
              using assms(23) by (fastforce simp add: filter_empty_conv)
            have x: "(\<lambda>s. if s = In \<or> s = Out then 0 else length (filter (\<lambda>x. port.side x = s) (pg_ports x))) = (\<lambda>s. 0)"
              using assms(21) by (fastforce simp add: filter_empty_conv)
            show ?thesis
              using e'(1) R(3)
              apply hypsubst
              apply (subst (1 2) u)
              apply (subst (1 2) x)
              apply (rule refl)
              done
          qed
          ultimately show ?thesis
            using that(6) by blast
        qed
      qed
      note parseq_cases = this

      show "renameEdge ?f e \<in> set (pg_edges ?seqpar)"
        using parseq_cases
      proof cases
        case XY
        have "renameEdge ?f e \<in> set (seqInterfaceEdges x' y')"
          using assms(8,11) XY
          apply (rule seqInterfaceEdges_set_rename)
          using renameEdge_f_x xx'(3) apply blast
          using renameEdge_f_y yy'(3) apply blast
          done
        then have "renameEdge ?f e \<in> set (seqInterfaceEdges (juxtapose x' u') (juxtapose y' v'))"
          using decompose_seqPar_interface by blast
        then show ?thesis
          by simp
      next
        case X
        then have "renameEdge ?f e \<in> set (pg_edges x')"
          using renameEdge_f_x xx'(3) by blast
        moreover have not_out: "\<not> toOpenOut (renameEdge ?f e)"
          using X(2) by simp
        ultimately have "renameEdge ?f e \<in> set (pg_edges (juxtapose x' u'))"
          by simp
        then have "renameEdge ?f e \<in>
          set (disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = Out) (pg_ports (juxtapose x' u')))) (pg_edges (juxtapose x' u')))"
          using not_out x'u'.disconnect_out by force
        then show ?thesis
          by (simp del: seqInterfaceEdges.simps juxtapose.simps)
      next
        case Y
        then have "renameEdge ?f e' \<in> set (pg_edges y')"
          using renameEdge_f_y yy'(3) by blast
        moreover have not_in: "\<not> fromOpenIn (renameEdge ?f e')"
          using Y(2) by simp
        ultimately have "renameEdge ?f e' \<in> set (pg_edges (juxtapose y' v'))"
          by simp
        then have "renameEdge ?f e' \<in>
          set (disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = In) (pg_ports (juxtapose y' v')))) (pg_edges (juxtapose y' v')))"
          using not_in y'v'.disconnect_in by force
        moreover have "shiftOpenInEdge ?shiftSeqX ?shiftSeqX e = shiftOpenInEdge ?shiftSeqX'U' ?shiftSeqX'U' e" for e
          unfolding juxtapose.simps port_graph.sel filter_append length_append filter_map comp_def length_map shiftPort_simps(2)
          unfolding len_fil_x
          apply (rule arg_cong2[where f = "\<lambda>x y. shiftOpenInEdge x y _"])
          using assms(23) uu'(5) apply (fastforce simp add: filter_empty_conv)
          using assms(23) uu'(5) apply (fastforce simp add: filter_empty_conv)
          done
        ultimately show ?thesis
          apply (simp del: seqInterfaceEdges.simps juxtapose.simps)
          apply (intro disjI2)
          apply (subst Y(3))
          apply (subst renameEdge_shiftOpenInEdge)
          apply (rule image_eqI)
           defer
           apply assumption
          apply (subst (1 2) renameEdge_shiftOpenInEdge[symmetric])
          apply (rule arg_cong[where f = "renameEdge _"])
          apply assumption
          done
      next
        case UV
        have "renameEdge ?f e' \<in> set (seqInterfaceEdges u' v')"
          using assms(9,12) UV(2)
          apply (rule seqInterfaceEdges_set_rename)
          using renameEdge_f_u uu'(3) apply blast
          using renameEdge_f_v vv'(3) apply blast
          done
        moreover have "e = shiftOpenInEdge ?shiftX' ?shiftY' e'"
        proof -
          have "place_side (edge_from e') = In" if "place_open (edge_from e')"
            using that by (metis UV(2) not_place_open seqInterfaceEdges_setD u.edge_from_cases)
          moreover have "place_side (edge_to e') = Out" if "place_open (edge_to e')"
            using that by (metis UV(2) not_place_open seqInterfaceEdges_setD v.edge_to_cases)
          ultimately show ?thesis
            apply (simp add: UV(1) len_fil_x len_fil_y)
            apply (subst (1 2) shiftOpenInEdge_known(1)[where s = In, unfolded place_side.simps], metis)
            apply (subst (1 2) shiftOpenInEdge_known(2)[where s = Out, unfolded place_side.simps], metis)
            apply simp
            apply (rule arg_cong[where f = "\<lambda>x. shiftOpenInEdge x _ _"])
            apply standard
            apply (subst (2) filter_False, blast)
            apply (metis (mono_tags, lifting) add.right_neutral filter_cong in_out_distinct list.size(3))
            done
        qed
        ultimately have "renameEdge ?f e \<in> shiftOpenInEdge ?shiftX' ?shiftY' ` set (seqInterfaceEdges u' v')"
          by simp
        then have "renameEdge ?f e \<in> set (seqInterfaceEdges (juxtapose x' u') (juxtapose y' v'))"
          using decompose_seqPar_interface by blast
        then show ?thesis
          by simp
      next
        case U
        then have "renameEdge ?f e' \<in> set (pg_edges u')"
          using renameEdge_f_u uu'(3) by blast
        moreover have "\<not> toOpenOut (renameEdge ?f e')"
          using U(3) by simp
        ultimately have "renameEdge ?f (shiftOpenInEdge ?shiftX' ?shiftX' e') \<in> set (pg_edges (juxtapose x' u'))"
          by simp
        moreover have "e = shiftOpenInEdge ?shiftX' ?shiftX' e'"
          unfolding U(1)
          apply simp
          apply (simp add: len_fil_x len_fil_y)
          apply (subst (1 2) shiftOpenInEdge_known(1)[where s = In])
          apply (metis U(2) assms(23) edge_in_flowI(2) u.edge_from_open u.edge_from_pg)
          apply (subst (1 2) shiftOpenInEdge_known(2)[where s = In])
           apply (metis U(2,3) assms(23) toOpenOutI u.edge_to_pg)
          apply (rule arg_cong2[where f = "\<lambda>x y. shiftOpenInEdge x y _"])
           apply standard
          apply (smt (verit, best) add.right_neutral empty_filter_conv filter_cong in_out_distinct list.size(3))
           apply standard
          apply (smt (verit, best) add.right_neutral empty_filter_conv filter_cong in_out_distinct list.size(3))
          done
        ultimately have "renameEdge ?f e \<in> set (pg_edges (juxtapose x' u'))"
          by metis
        moreover have "\<not> toOpenOut (renameEdge ?f e)"
          using U(1,3) by simp
        ultimately have "renameEdge ?f e \<in>
          set (disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = Out) (pg_ports (juxtapose x' u')))) (pg_edges (juxtapose x' u')))"
          using x'u'.disconnect_out by simp
        then show ?thesis
          by (simp del: seqInterfaceEdges.simps juxtapose.simps)
      next
        case V
        then have "renameEdge ?f e' \<in> set (pg_edges v')"
          using renameEdge_f_v vv'(3) by blast
        moreover have not_in: "\<not> fromOpenIn (renameEdge ?f e')"
          using V(2) by simp
        ultimately have "renameEdge ?f (shiftOpenInEdge ?shiftY' ?shiftY' e') \<in> set (pg_edges (juxtapose y' v'))"
          by simp
        then have "renameEdge ?f (shiftOpenInEdge ?shiftY' ?shiftY' e') \<in>
          set (disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = In) (pg_ports (juxtapose y' v')))) (pg_edges (juxtapose y' v')))"
          using not_in y'v'.disconnect_in by force
        moreover have
          " shiftOpenInEdge ?shiftXY ?shiftXY (shiftOpenInEdge ?shiftSeqX ?shiftSeqX e')
          = shiftOpenInEdge ?shiftSeqX'U' ?shiftSeqX'U' (shiftOpenInEdge ?shiftY' ?shiftY' e')"
        proof -
          have "place_ground (edge_from e')"
            using V(1,2) assms(24) v.edge_from_open v.edge_from_pg
            by (meson edge_in_flowI(2) fromOpenInI not_place_open)
          then have
            " shiftOpenPlace ?shiftXY (shiftOpenPlace ?shiftSeqX (edge_from e'))
            = shiftOpenPlace ?shiftSeqX'U' (shiftOpenPlace ?shiftY' (edge_from e'))"
            by simp
          moreover have "place_open (edge_to e') \<Longrightarrow> place_side (edge_to e') = Out"
            using V(1) assms(24) edge_in_flowI(3) v.edge_to_open v.edge_to_pg by blast
          then have
            " shiftOpenPlace ?shiftXY (shiftOpenPlace ?shiftSeqX (edge_to e'))
            = shiftOpenPlace ?shiftSeqX'U' (shiftOpenPlace ?shiftY' (edge_to e'))"
            by (subst (1 2 3 4) shiftOpenPlace_known[where s = Out])
               (simp_all add: len_fil_y)
          ultimately show ?thesis
            by (metis (no_types, lifting) shiftOpenInEdge_def shiftOpenInEdge_simps)
        qed
        ultimately show ?thesis
          apply (simp del: seqInterfaceEdges.simps juxtapose.simps)
          apply (intro disjI2)
          apply (subst V(3))
          apply (subst renameEdge_shiftOpenInEdge)
          apply (rule image_eqI)
           defer
           apply assumption
          apply (subst renameEdge_shiftOpenInEdge[symmetric])+
          apply (rule arg_cong[where f = "renameEdge _"])
          apply simp
          done
      qed
      moreover have "e = renameEdge ?g (renameEdge ?f e)"
      proof (cases rule: parseq_cases)
        case XY
        then show ?thesis
          using inv_on_places_x inv_on_places_y x.edge_from_pg y.edge_to_pg
          by (smt (verit) edge.expand renameEdge_simps(2,3) seqInterfaceEdges_setD)
      next
        case X
        then show ?thesis
          using inv_on_edges_x by presburger
      next
        case Y
        then show ?thesis
          by (metis (no_types, lifting) inv_on_edges_y renameEdge_shiftOpenInEdge)
      next
        case UV
        then show ?thesis
        using inv_on_edges_u inv_on_edges_v
        by (smt (verit, ccfv_SIG) edge.expand renameEdge_shiftOpenInEdge renameEdge_simps(2,3) seqInterfaceEdges_setD)
      next
        case U
        then show ?thesis
          by (metis (no_types, lifting) inv_on_edges_u renameEdge_shiftOpenInEdge)
      next
        case V
        then show ?thesis
          by (metis (no_types, lifting) inv_on_edges_v renameEdge_shiftOpenInEdge)
      qed
      ultimately show "e \<in> renameEdge ?g ` set (pg_edges ?seqpar)"
        by blast
    next
      fix e
      assume "e \<in> set (pg_edges ?seqpar)"
      then consider
        "e \<in> set (seqInterfaceEdges (juxtapose x' u') (juxtapose y' v'))"
        | "e \<in> set (pg_edges (juxtapose x' u'))" and "\<not> toOpenOut e"
        | e' where "e = shiftOpenInEdge ?shiftSeqX'U' ?shiftSeqX'U' e'" and "e' \<in> set (pg_edges (juxtapose y' v'))" and "\<not> fromOpenIn e'"
        using seqPortGraphs_edge_cases pgf_x'u' pgf_y'v' by blast
      then consider
        "e \<in> set (seqInterfaceEdges x' y')"
        | e' where "e = shiftOpenInEdge ?shiftX' ?shiftY' e'" and "e' \<in> set (seqInterfaceEdges u' v')"
        | "e \<in> set (pg_edges (juxtapose x' u'))" and "\<not> toOpenOut e"
        | e' where "e = shiftOpenInEdge ?shiftSeqX'U' ?shiftSeqX'U' e'" and "e' \<in> set (pg_edges (juxtapose y' v'))" and "\<not> fromOpenIn e'"
        using decompose_seqPar_interface by blast
      then consider
         (XY) a b and p :: "('s, 'a) port"
          where "edge_from e = edge_from a" and "a \<in> set (pg_edges x')"
            and "edge_to e = edge_to b" and "b \<in> set (pg_edges y')"
            and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
            and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
            and "port.side p = Out"
        | (UV) e' a b and p :: "('s, 'a) port"
          where "e = shiftOpenInEdge ?shiftX' ?shiftY' e'"
            and "edge_from e' = edge_from a" and "a \<in> set (pg_edges u')"
            and "edge_to e' = edge_to b" and "b \<in> set (pg_edges v')"
            and "edge_to a = OpenPort (portSetSide Out p)" and "edge_in_flow a"
            and "edge_from b = OpenPort (portSetSide In p)" and "edge_in_flow b"
            and "port.side p = Out"
        | (X) "e \<in> set (pg_edges x')" and "\<not> toOpenOut e"
        | (U) e'
          where "e = shiftOpenInEdge ?shiftX' ?shiftX' e'" and "e' \<in> set (pg_edges u')" and "\<not> toOpenOut e'"
        | (Y) e'
          where "e = shiftOpenInEdge ?shiftSeqX'U' ?shiftSeqX'U' e'" and "e' \<in> set (pg_edges y')" and "\<not> fromOpenIn e'"
        | (V) e'
          where "e = shiftOpenInEdge ?shiftSeqX'U' ?shiftSeqX'U' (shiftOpenInEdge ?shiftY' ?shiftY' e')"
            and "e' \<in> set (pg_edges v')" and "\<not> fromOpenIn e'"
      proof cases
           case 1 then show ?thesis using that(1) by (blast elim: seqInterfaceEdges_setD)
      next case 2 then show ?thesis using that(2) by (blast elim: seqInterfaceEdges_setD)
      next case 3 then show ?thesis using that(3,4) by fastforce
      next case 4 then show ?thesis using that(5,6) by fastforce
      qed
      note seqpar_cases = this

      show "renameEdge ?g e \<in> set (pg_edges ?parseq)"
      proof (cases rule: seqpar_cases)
        case XY
        have "renameEdge ?g e \<in> set (seqInterfaceEdges x y)"
          using assms(1,2)
        proof (rule seqInterfaceEdges_setI)
          show "edge_from (renameEdge ?g e) = edge_from (renameEdge ?g a)"
            by (simp add: XY(1))
          show "renameEdge ?g a \<in> set (pg_edges x)"
            using XY(2) renameEdge_g_x xx'(4) by blast
          show "edge_to (renameEdge ?g e) = edge_to (renameEdge ?g b)"
            by (simp add: XY(3))
          show "renameEdge ?g b \<in> set (pg_edges y)"
            using XY(4) renameEdge_g_y yy'(4) by blast
          show "edge_to (renameEdge ?g a) = OpenPort (portSetSide Out p)"
            by (simp add: XY(5))
          show "edge_from (renameEdge ?g b) = OpenPort (portSetSide In p)"
            by (simp add: XY(7))
        qed
        then show ?thesis
          by force
      next
        case UV
        have "renameEdge ?g e' \<in> set (pg_edges (seqPortGraphs u v))"
        proof -
          have "renameEdge ?g e' \<in> set (seqInterfaceEdges u v)"
            using assms(4,5)
          proof (rule seqInterfaceEdges_setI)
            show "edge_from (renameEdge ?g e') = edge_from (renameEdge ?g a)"
              by (simp add: UV(2))
            show "renameEdge ?g a \<in> set (pg_edges u)"
              using UV(3) renameEdge_g_u uu'(4) by blast
            show "edge_to (renameEdge ?g e') = edge_to (renameEdge ?g b)"
              by (simp add: UV(4))
            show "renameEdge ?g b \<in> set (pg_edges v)"
              using UV(5) renameEdge_g_v vv'(4) by blast
            show "edge_to (renameEdge ?g a) = OpenPort (portSetSide Out p)"
              by (simp add: UV(6))
            show "edge_from (renameEdge ?g b) = OpenPort (portSetSide In p)"
              by (simp add: UV(8))
          qed
          then show ?thesis
            by simp
        qed
        moreover have "e = shiftOpenInEdge ?shiftXY ?shiftXY e'"
          unfolding UV(1)
          apply (subst (1 2) shiftOpenInEdge_known(1)[where s = In])
          using UV(2) UV(3) UV(7) u'.edge_from_open apply force
          apply (subst (1 2) shiftOpenInEdge_known(2)[where s = Out])
          using UV(4) UV(5) UV(9) v'.edge_to_open apply force
          apply (simp add: len_fil_x len_fil_y)
          apply (rule arg_cong[where f = "\<lambda>x. shiftOpenInEdge x _ _"])
          by (metis (mono_tags, lifting) filter_cong in_out_distinct)
        ultimately show ?thesis
          unfolding juxtapose.simps port_graph.sel set_append set_map
          by fastforce
      next
        case X
        then have "renameEdge ?g e \<in> set (pg_edges x)"
          using renameEdge_g_x xx'(4) by blast
        then have "renameEdge ?g e \<in> set (disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = Out) (pg_ports x))) (pg_edges x))"
          by (simp add: X(2) x.disconnect_out)
        then have "renameEdge ?g e \<in> set (pg_edges (seqPortGraphs x y))"
          by simp
        then show ?thesis
          by fastforce
      next
        case U
        then have "renameEdge ?g e' \<in> set (pg_edges u)"
          using renameEdge_g_u uu'(4) by blast
        then have "renameEdge ?g e' \<in> set (disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = Out) (pg_ports u))) (pg_edges u))"
          by (simp add: U(3) u.disconnect_out)
        then have "renameEdge ?g e' \<in> set (pg_edges (seqPortGraphs u v))"
          by simp
        moreover have "e = shiftOpenInEdge ?shiftXY ?shiftXY e'"
        proof -
          have "place_ground (edge_to e')"
            using U(2) U(3) uu'(4) assms(23) u'.edge_to_cases u.edge_to_pg
            by (metis (no_types, opaque_lifting) edge_in_flowI(3) image_iff not_place_open renameEdge_simps(3) renamePlace_simps(2) toOpenOutI)
          then have
            " shiftOpenPlace ?shiftX' (edge_to e')
            = shiftOpenPlace ?shiftXY (edge_to e')"
            by simp
          moreover have "place_open (edge_from e') \<Longrightarrow> place_side (edge_from e') = In"
            using U(2) uu'(4) assms(23) u'.edge_from_open u.edge_from_pg
            by (metis (no_types, opaque_lifting) edge_in_flowI(2) image_iff renameEdge_simps(2) renamePlace_simps(2))
          then have
            " shiftOpenPlace ?shiftX' (edge_from e')
            = shiftOpenPlace ?shiftXY (edge_from e')"
            apply (subst (1 2) shiftOpenPlace_known[where s = In])
            apply (simp_all add: len_fil_x)
            by (metis (mono_tags, lifting) filter_cong in_out_distinct)
          ultimately show ?thesis
            using U(1) by (metis shiftOpenInEdge_def)
        qed
        ultimately show ?thesis
          unfolding juxtapose.simps port_graph.sel set_append set_map
          apply (intro UnI2)
          by (smt (verit, best) image_iff renameEdge_shiftOpenInEdge)
      next
        case Y
        then have "renameEdge ?g e' \<in> set (pg_edges y)"
          using renameEdge_g_y yy'(4) by blast
        then have "renameEdge ?g e' \<in> set (disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = In) (pg_ports y))) (pg_edges y))"
          using Y(3) y.disconnect_in by auto
        then have "shiftOpenInEdge ?shiftSeqX ?shiftSeqX (renameEdge ?g e') \<in> set (pg_edges (seqPortGraphs x y))"
          unfolding seqPortGraphs.simps port_graph.sel set_append set_map image_Un image_renameEdge_shiftOpenInEdge
          by (intro UnI2 imageI)
        moreover have "e = shiftOpenInEdge ?shiftSeqX ?shiftSeqX e'"
        proof -
          have "place_open (edge_from e') \<Longrightarrow> place_side (edge_from e') = In"
            using Y(2) yy'(4) assms(22) y'.edge_from_open y.edge_from_pg
            by (metis (no_types, opaque_lifting) edge_in_flowI(2) image_iff place_open_def renameEdge_simps(2) renamePlace.simps(2))
          then have
            " shiftOpenPlace ?shiftSeqX'U' (edge_from e')
            = shiftOpenPlace ?shiftSeqX (edge_from e')"
            by (simp add: shiftOpenPlace_known)
          moreover have "place_open (edge_to e') \<Longrightarrow> place_side (edge_to e') = Out"
            using Y(2) yy'(4) assms(22) y.edge_to_pg y.edge_to_open
            by (metis edge_in_flowI(3) image_eqI renameEdge_simps(3) renamePlace_simps(2))
          then have
            " shiftOpenPlace ?shiftSeqX'U' (edge_to e')
            = shiftOpenPlace ?shiftSeqX (edge_to e')"
            by (simp add: shiftOpenPlace_known)
          ultimately show ?thesis
            by (simp add: Y(1) shiftOpenInEdge_def)
        qed
        ultimately show ?thesis
          unfolding juxtapose.simps port_graph.sel set_append set_map
          apply (intro UnI1)
          by (smt (verit, best) image_iff renameEdge_shiftOpenInEdge)
      next
        case V
        then have "renameEdge ?g e' \<in> set (pg_edges v)"
          using renameEdge_g_v vv'(4) by blast
        then have "renameEdge ?g e' \<in> set (disconnectFromPlaces (map OpenPort (filter (\<lambda>x. port.side x = In) (pg_ports v))) (pg_edges v))"
          using V(3) v.disconnect_in by auto
        then have "shiftOpenInEdge ?shiftSeqU ?shiftSeqU (renameEdge ?g e') \<in> set (pg_edges (seqPortGraphs u v))"
          unfolding seqPortGraphs.simps port_graph.sel set_append set_map image_Un image_renameEdge_shiftOpenInEdge
          by (intro UnI2 imageI)
        moreover have "e = shiftOpenInEdge ?shiftXY ?shiftXY (shiftOpenInEdge ?shiftSeqU ?shiftSeqU e')"
        proof -
          have "place_ground (edge_from e')"
            using V(2,3) sides_v' v'.edge_from_open v'.edge_from_pg
            by (meson edge_in_flowI(2) fromOpenInI place.exhaust_disc)
          then have
            " shiftOpenPlace ?shiftXY (shiftOpenPlace ?shiftSeqU (edge_from e'))
            = shiftOpenPlace ?shiftSeqX'U' (shiftOpenPlace ?shiftY' (edge_from e'))"
            by simp
          moreover have "place_open (edge_to e') \<Longrightarrow> place_side (edge_to e') = Out"
            using V(2) sides_v' v'.edge_to_pg v'.edge_to_open
            by (meson edge_in_flowI(3))
          then have
            " shiftOpenPlace ?shiftXY (shiftOpenPlace ?shiftSeqU (edge_to e'))
            = shiftOpenPlace ?shiftSeqX'U' (shiftOpenPlace ?shiftY' (edge_to e'))"
            by (subst (1 2 3 4) shiftOpenPlace_known[where s = Out])
               (simp_all add: len_fil_y)
          ultimately show ?thesis
            using V(1) by (metis (no_types, lifting) shiftOpenInEdge_def shiftOpenInEdge_simps)
        qed
        ultimately show ?thesis
          unfolding juxtapose.simps port_graph.sel set_append set_map
          apply (intro UnI2)
          by (smt (verit, best) image_iff renameEdge_shiftOpenInEdge)
      qed
      moreover have "e = renameEdge ?f (renameEdge ?g e)"
      proof (cases rule: seqpar_cases)
        case XY
        then show ?thesis
          using inv_on_places_x' inv_on_places_y' x'.edge_from_pg y'.edge_to_pg
          by (metis (no_types, lifting) edge.expand renameEdge_simps(2,3))
      next
        case UV
        then show ?thesis
          using inv_on_places_u' inv_on_places_v' u'.edge_from_pg v'.edge_to_pg
          by (smt (verit, best) edge.expand renameEdge_shiftOpenInEdge renameEdge_simps(2) renameEdge_simps(3))
      next case X then show ?thesis using inv_on_edges_x' by presburger
      next case U then show ?thesis using inv_on_edges_u' by force
      next case Y then show ?thesis using inv_on_edges_y' by force
      next case V then show ?thesis using inv_on_edges_v' by force
      qed
      ultimately show "e \<in> renameEdge ?f ` set (pg_edges ?parseq)"
        by blast
    qed
  qed
  moreover have "\<And>l. l \<in> node_name ` set (pg_nodes ?parseq) \<Longrightarrow> ?g (?f l) = l"
    apply (elim imageE in_nodes_juxtaposeE in_nodes_seqPortGraphsE)
    using xx'(1,6) renameNode_f_x renameNode_g_x apply (smt (z3) imageI renameNode_simps(2))
    using yy'(1,6) renameNode_f_y renameNode_g_y apply (smt (z3) imageI renameNode_simps(2))
    using uu'(1,6) renameNode_f_u renameNode_g_u apply (smt (z3) imageI renameNode_simps(2))
    using vv'(1,6) renameNode_f_v renameNode_g_v apply (smt (z3) imageI renameNode_simps(2))
    done
  moreover have "\<And>l. l \<in> node_name ` set (pg_nodes ?seqpar) \<Longrightarrow> ?f (?g l) = l"
    apply (elim imageE in_nodes_juxtaposeE in_nodes_seqPortGraphsE)
    using xx'(2,7) renameNode_f_x renameNode_g_x apply (smt (z3) imageI renameNode_simps(2))
    using uu'(2,7) renameNode_f_u renameNode_g_u apply (smt (z3) imageI renameNode_simps(2))
    using yy'(2,7) renameNode_f_y renameNode_g_y apply (smt (z3) imageI renameNode_simps(2))
    using vv'(2,7) renameNode_f_v renameNode_g_v apply (smt (z3) imageI renameNode_simps(2))
    done
  ultimately have "pgEquiv_witness ?f ?g (juxtapose (seqPortGraphs x y) (seqPortGraphs u v)) (seqPortGraphs (juxtapose x' u') (juxtapose y' v'))"
    by (rule pgEquiv_witnessI)
  then show "\<exists>f g. pgEquiv_witness f g (juxtapose (seqPortGraphs x y) (seqPortGraphs u v)) (seqPortGraphs (juxtapose x' u') (juxtapose y' v'))"
    by blast
qed

end