theory Map3
  imports Main
begin

section\<open>Three-way Mapper\<close>

text\<open>
  We define an alternative to @{const map2} over three lists instead of two.
  The motivation is constructing a list of labelled edges from lists of origins, destinations and
  labels, but the mechanisation is general to allow for other uses.
\<close>

definition map3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list"
  where "map3 f xs ys zs = map (\<lambda>(x, y, z). f x y z) (zip xs (zip ys zs))"

lemma map3_Nil [simp]:
  "map3 f [] ys zs = []"
  "map3 f xs [] zs = []"
  "map3 f xs ys [] = []"
  by (simp_all add: map3_def)

lemma set_map3 [simp]:
  "set (map3 f xs ys zs) = (\<lambda>(x, y, z). f x y z) ` set (zip xs (zip ys zs))"
  by (simp add: map3_def)

lemma map_map3:
  "map g (map3 f xs ys zs) = map3 (\<lambda>x y z. g (f x y z)) xs ys zs"
  by (clarsimp simp add: map3_def)

lemma zip_map2_as_map3:
  "zip xs (map2 f ys zs) = map3 (\<lambda>x y z. (x, f y z)) xs ys zs"
  "zip (map2 f xs ys) zs = map3 (\<lambda>x y. Pair (f x y)) xs ys zs"
proof -
  show "zip xs (map2 f ys zs) = map3 (\<lambda>x y z. (x, f y z)) xs ys zs"
    by (simp add: map3_def prod.case_distrib zip_map2)
  show "zip (map2 f xs ys) zs = map3 (\<lambda>x y. Pair (f x y)) xs ys zs"
    by (clarsimp simp add: map3_def zip_map1 zip_assoc)
qed

lemma zip_map3:
  "zip (map f xs) (zip (map g ys) (map h zs)) = map3 (\<lambda>x y z. (f x, g y, h z)) xs ys zs"
  "zip (zip (map f xs) (map g ys)) (map h zs) = map3 (\<lambda>x y z. ((f x, g y), h z)) xs ys zs"
proof -
  have
    " zip (map f xs) (zip (map g ys) (map h zs)) = map3 (\<lambda>x y z. (f x, g y, h z)) xs ys zs
    \<and> zip (zip (map f xs) (map g ys)) (map h zs) = map3 (\<lambda>x y z. ((f x, g y), h z)) xs ys zs"
  proof (induct xs arbitrary: ys zs)
    case Nil
    then show ?case by (simp add: map3_def)
  next
    case xs: (Cons x xs)
    then show ?case
    proof (cases ys)
      case Nil
      then show ?thesis by (simp add: map3_def)
    next
      case ys: (Cons b bs)
      then show ?thesis
      proof (cases zs)
        case Nil
        then show ?thesis by (simp add: map3_def)
      next
        case (Cons c cs)
        then show ?thesis using xs ys by (simp add: map3_def)
      qed
    qed
  qed
  then show "zip (map f xs) (zip (map g ys) (map h zs)) = map3 (\<lambda>x y z. (f x, g y, h z)) xs ys zs"
        and "zip (zip (map f xs) (map g ys)) (map h zs) = map3 (\<lambda>x y z. ((f x, g y), h z)) xs ys zs"
    by metis+
qed

lemma map3_map:
  "map3 f (map a xs) (map b xs) (map c xs) = map (\<lambda>x. f (a x) (b x) (c x)) xs"
  by (induct xs) (simp_all add: map3_def)

lemma map3_map_each:
  "map3 f (map a xs) (map b ys) (map c zs) = map3 (\<lambda>x y z. f (a x) (b y) (c z)) xs ys zs"
proof (induct xs arbitrary: ys zs)
  case Nil
  then show ?case by (simp add: map3_def)
next
  case xs: (Cons x xs)
  then show ?case
  proof (cases ys)
    case Nil
    then show ?thesis by (simp add: map3_def)
  next
    case ys: (Cons b bs)
    then show ?thesis
    proof (cases zs)
      case Nil
      then show ?thesis by (simp add: map3_def)
    next
      case (Cons c cs)
      then show ?thesis using xs ys by (simp add: map3_def)
    qed
  qed
qed

lemma in_set_map3E:
  assumes "a \<in> set (map3 f xs ys zs)"
  obtains x y z i
  where "a = f x y z" and "xs ! i = x" and "ys ! i = y" and "zs ! i = z" and "i < length xs" and "i < length ys" and "i < length zs"
proof -
  have "a \<in> (\<lambda>x. case x of (x, y, z) \<Rightarrow> f x y z) ` set (zip xs (zip ys zs))"
    using assms by simp
  then obtain x y z where "a = f x y z" and "(x, y, z) \<in> set (zip xs (zip ys zs))"
    by force
  then show thesis
    using that by (fastforce simp add: in_set_zip)
qed

end