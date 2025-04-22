theory Util
  imports Main
begin

section\<open>Utility Theorems\<close>

text\<open>
  This theory contains general facts that we use in our proof but which do not depend on our
  development.
\<close>

text\<open>Using @{thm in_set_zip} we can characterise an element of @{term "map2 f xs ys"}.\<close>
lemma in_set_map2E:
  assumes "z \<in> set (map2 f xs ys)"
  obtains x y i
  where "z = f x y" and "xs ! i = x" and "ys ! i = y" and "i < length xs" and "i < length ys"
proof -
  have "z \<in> (\<lambda>x. case x of (x, xa) \<Rightarrow> f x xa) ` set (zip xs ys)"
    using assms by simp
  then obtain x y where "z = f x y" and "(x, y) \<in> set (zip xs ys)"
    by force
  then show thesis
    using that by (fastforce simp add: in_set_zip)
qed

text\<open>
  When using @{const map2} on lists that are themselves results of mapping we can combine all three
  functions.
\<close>
lemma map2_map_each:
  "map2 f (map gl xs) (map gr ys) = map2 (\<lambda>x y. f (gl x) (gr y)) xs ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (induct ys ; simp)
qed

end