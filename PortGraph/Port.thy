theory Port
  imports Main
begin

section\<open>Ports\<close>

text\<open>
  Ports are objects existing in relation to something larger, such as a node in a port graph, to
  which they are attached.
  Usually, they mediate some kind of connection.
  As such, they bring together a side (where they attach to the larger object), an index within
  that side (to distinguish multiple ports attached to one side) and an arbitrary label (to carry
  any additional data).
  To allow for ports of many objects in one concepts, they can be paired with names (themselves
  sequences of name atoms) which can then be qualified to distinguish them.

  This theory establishes this basic notion of ports and basic operations with them.
\<close>

subsection\<open>Ports\<close>

text\<open>Port is on a side, at some index and carries some label\<close>
datatype ('s, 'a) port = Port (side: 's) (index: nat) (label: 'a)
hide_const (open) side index label

text\<open>Initial index, a side and a list of labels can be turned into a list of ports on that side\<close>
fun listPorts :: "nat \<Rightarrow> 's \<Rightarrow> 'a list \<Rightarrow> ('s, 'a) port list"
  where "listPorts n s as = map (case_prod (Port s)) (zip [n..< n + length as] as)"

text\<open>This produces as many ports as there were labels provided\<close>
lemma listPorts_length [simp]:
  "length (listPorts n s as) = length as"
  by simp

text\<open>Due to the incrementing index, turning a list into ports makes the elements distinct\<close>
lemma distinct_listPorts [simp]:
  "distinct (listPorts n s as)"
  by (fastforce intro: inj_onI simp add: distinct_map distinct_zipI1)

text\<open>Two port lists generated with different sides cannot intersect\<close>
lemma listPorts_distinct_sides_no_inter [simp]:
  assumes "s \<noteq> s'"
    shows "set (listPorts n s xs) \<inter> set (listPorts n' s' ys) = {}"
  using assms by fastforce

text\<open>Append in the list of labels can be decomposed to make two lists of ports\<close>
lemma listPorts_append:
  "listPorts n s (a @ b) = listPorts n s a @ listPorts (n + length a) s b"
  by (simp add: add.assoc zip_append2)

text\<open>Any element of the result is simply determined by its index and the inputs\<close>
lemma nth_listPorts [simp]:
  "i < length xs \<Longrightarrow> listPorts n s xs ! i = Port s (n + i) (xs ! i)"
  by simp

text\<open>There are two possible cases when filtering @{const listPorts} by port sides\<close>
lemma filter_port_side_listPorts [simp]:
  "s = t \<Longrightarrow> filter (\<lambda>x. port.side x = s) (listPorts n t r) = listPorts n s r"
  "s \<noteq> t \<Longrightarrow> filter (\<lambda>x. port.side x = s) (listPorts n t r) = []"
  by (simp_all add: filter_map comp_def split_def)

text\<open>Set side of a port\<close>
primrec portSetSide :: "'s \<Rightarrow> ('t, 'a) port \<Rightarrow> ('s, 'a) port"
  where "portSetSide side (Port s i r) = Port side i r"

lemma
  shows portSetSide_side [simp]: "port.side (portSetSide s x) = s"
    and portSetSide_index [simp]: "port.index (portSetSide s x) = port.index x"
    and portSetSide_label [simp]: "port.label (portSetSide s x) = port.label x"
  by (cases x, simp)+

text\<open>Setting the port side twice is the same as just the latter one\<close>
lemma portSetSide_absorb [simp]:
  "portSetSide x (portSetSide y p) = portSetSide x p"
  by (cases p) simp

text\<open>Setting port side to its present value is identity\<close>
lemma portSetSide_same [simp]:
  "port.side p = s \<Longrightarrow> portSetSide s p = p"
  by (cases p) simp

text\<open>Setting port side on the result of @{const listPorts} is the same as changing its argument\<close>
lemma portSetSide_listPorts [simp]:
  "map (portSetSide s) (listPorts n s' xs) = listPorts n s xs"
  by (induct xs ; clarsimp)

subsection\<open>Qualified Ports\<close>

text\<open>Qualified port is a basic port along with a sequence of name atoms\<close>
datatype ('s, 'a, 'n) qualified_port = QPort (port: "('s, 'a) port") (name: "'n list")
hide_const (open) port name

text\<open>Rename a qualified port with any function on names\<close>
primrec renameQPort ::
    "('m list \<Rightarrow> 'n list) \<Rightarrow> ('s, 'a, 'm) qualified_port \<Rightarrow> ('s, 'a, 'n) qualified_port"
  where "renameQPort f (QPort port path) = QPort port (f path)"

lemma renameQPort_simps [simp]:
  "qualified_port.port (renameQPort f x) = qualified_port.port x"
  "qualified_port.name (renameQPort f x) = f (qualified_port.name x)"
  by (cases x, simp)+

text\<open>Renaming with identity is identity\<close>
lemma renameQPort_id [simp]:
  "renameQPort id = id"
proof
  fix x :: "('x, 'y, 'z) qualified_port"
  show "renameQPort id x = id x"
    by (cases x ; simp)
qed

text\<open>
  Renaming is injective on a set of qualified ports if the function is injective on the set of their
  names
\<close>
lemma renameQPort_inj_on:
    fixes f :: "'m list \<Rightarrow> 'n list"
      and A :: "('s, 'a, 'm) qualified_port set"
  assumes "inj_on f (qualified_port.name ` A)"
    shows "inj_on (renameQPort f) A"
proof
  fix x y :: "('s, 'a, 'm) qualified_port"
  assume "renameQPort f x = renameQPort f y"
     and "x \<in> A" and "y \<in> A"
  then show "x = y"
    using assms
    by (metis (mono_tags, lifting) image_eqI inj_on_def qualified_port.expand renameQPort_simps)
qed

lemma renameQPort_inj:
  "inj f \<Longrightarrow> inj (renameQPort f)"
  using renameQPort_inj_on by (metis inj_on_subset top_greatest)

text\<open>Renaming with the inverse of a bijection is the inverse renaming\<close>
lemma renameQPort_inv [simp]:
  fixes f :: "'m list \<Rightarrow> 'n list"
  assumes "bij f"
  shows "renameQPort (inv f) = inv (renameQPort f)"
proof (intro inv_equality[symmetric])
  fix x :: "('x, 'y, 'm) qualified_port"
  obtain port path where "x = QPort port path"
    using qualified_port.exhaust by blast
  then show "renameQPort (inv f) (renameQPort f x) = x"
    using assms by (simp add: bij_is_inj)
next
  fix y :: "('x, 'y, 'n) qualified_port"
  obtain port path where "y = QPort port path"
    using qualified_port.exhaust by blast
  then show "renameQPort f (renameQPort (inv f) y) = y"
    using assms by (simp add: bij_is_surj surj_f_inv_f)
qed

text\<open>Renaming with a composition of functions is the composition of renamings\<close>
lemma renameQPort_comp [simp]:
  "renameQPort (g \<circ> f) = renameQPort g \<circ> renameQPort f"
proof
  fix x :: "('a, 'b, 'c) qualified_port"
  show "renameQPort (g \<circ> f) x = (renameQPort g \<circ> renameQPort f) x"
    by (cases x) simp
qed

text\<open>Renaming twice is the same as renaming with their composition\<close>
lemma renameQPort_twice [simp]:
  "renameQPort g (renameQPort f x) = renameQPort (\<lambda>x. g (f x)) x"
  by (cases x; simp)

text\<open>Further qualify a port with a name atom\<close>
primrec qualifyQPort :: "'n \<Rightarrow> ('s, 'a, 'n) qualified_port \<Rightarrow> ('s, 'a, 'n) qualified_port"
  where "qualifyQPort x (QPort port path) = QPort port (x # path)"

lemma qualifyQPort_simps [simp]:
  "qualified_port.port (qualifyQPort a x) = qualified_port.port x"
  "qualified_port.name (qualifyQPort a x) = a # (qualified_port.name x)"
  by (cases x, simp)+

text\<open>Qualifying a port is the same as renaming it with cons of that name atom\<close>
lemma qualifyQPort_rename:
  "qualifyQPort x p = renameQPort ((#) x) p"
  by (cases p) simp

text\<open>Drop some number of name atoms from a qualified port, (partially) unqualifying it\<close>
primrec unqualifyQPort :: "nat \<Rightarrow> ('s, 'a, 'p) qualified_port \<Rightarrow> ('s, 'a, 'p) qualified_port"
  where "unqualifyQPort n (QPort port path) = QPort port (drop n path)"

lemma unqualifyQPort_simps [simp]:
  "qualified_port.port (unqualifyQPort n x) = qualified_port.port x"
  "qualified_port.name (unqualifyQPort n x) = drop n (qualified_port.name x)"
  by (cases x, simp)+

text\<open>Unqualifying a port is the same as renaming it with @{const drop}\<close>
lemma unqualifyQPort_rename:
  "unqualifyQPort x p = renameQPort (drop x) p"
  by (cases p) simp

text\<open>Dropping a single element from the name of a port is the (left) inverse of qualifying it\<close>
lemma unqualify_qualify_qport_inv [simp]:
  "unqualifyQPort 1 (qualifyQPort n x) = x"
  by (cases x) simp

subsection\<open>Sides With Input and Output\<close>

text\<open>
  While we allow the sides to be arbitrary in general, often there are two distinguished sides:
  input and output.
  To allow these to be referenced in a reusable way, we define a type class that fixes the two
  elements and requires them to be distinct.
\<close>
class side_in_out =
  fixes In :: 'a
    and Out :: 'a
  assumes in_out_distinct: "In \<noteq> Out"
begin

lemmas [simp] = in_out_distinct in_out_distinct[symmetric]

end

end
