theory Util_Mapping
  imports
    "HOL-Library.Mapping"
    "HOL-Library.AList_Mapping"
begin

section\<open>Utility Theorems - Mappings\<close>

text\<open>
  This theory contains facts specifically about mappings that we use in our proofs but which do not
  depend on our development.
\<close>

text\<open>Deleting commutes with mapping of values\<close>
lemma delete_map_values:
  "Mapping.delete k (Mapping.map_values f m) = Mapping.map_values f (Mapping.delete k m)"
  by (metis Mapping.delete_update(1) Mapping_delete_if_notin_keys empty_iff keys_empty keys_is_none_rep
      keys_map_values lookup_delete map_values_update update_delete)

text\<open>Mapping and then deleting entry is the same as just deleting it\<close>
lemma delete_map_entry [simp]:
  "Mapping.delete k (Mapping.map_entry k f m) = Mapping.delete k m"
  by (cases "Mapping.lookup m k") (simp_all add: map_entry_code delete_update)

text\<open>Mapping values of empty mapping does nothing\<close>
lemma map_values_empty [simp]:
  "Mapping.map_values f Mapping.empty = Mapping.empty"
  by transfer simp

text\<open>Mapping values twice is the same as mapping with composed function\<close>
lemma map_values_comp:
  "Mapping.map_values g (Mapping.map_values f xs) = Mapping.map_values (\<lambda>k. g k \<circ> f k) xs"
  by transfer (simp add: option.map_comp)

text\<open>Mapping values is identity if the function is identity for everything present\<close>
lemma map_values_is_idI:
  assumes "\<And>x y. Mapping.lookup xs x = Some y \<Longrightarrow> f x y = y"
    shows "Mapping.map_values f xs = xs"
  using assms by transfer (simp add: map_option_cong option.map_ident)

text\<open>Entries after mapping are an image of the original entries\<close>
lemma entries_map_values:
  "Mapping.entries (Mapping.map_values f m) = (\<lambda>(k, v). (k, f k v)) ` Mapping.entries m"
  by transfer (fastforce simp add: graph_def)

text\<open>
  Entries after possibly @{const Mapping.default} are the original entries, possibly with the
  default value inserted
\<close>
lemma entries_default:
  "Mapping.entries (Mapping.default k v m) = (if k \<in> Mapping.keys m then Mapping.entries m else insert (k, v) (Mapping.entries m))"
  unfolding Mapping.default_def
proof transfer
  fix m :: "'a \<Rightarrow> 'b option" and k v
  show "Map.graph (if k \<in> dom m then m else m(k \<mapsto> v)) = (if k \<in> dom m then Map.graph m else insert (k, v) (Map.graph m))"
  proof (cases "k \<in> dom m")
    case True
    then show ?thesis by (simp add: graph_def)
  next
    case False
    then show ?thesis
      by (simp add: graph_def)
         (smt (verit, best) case_prodD case_prodI2 domIff insert_iff mem_Collect_eq option.inject option.simps(3) prod.inject subsetI subset_antisym)
  qed
qed

text\<open>Entries after mapping one entry are the original entries, possibly with the mapped entry replaced\<close>
lemma entries_map_entry:
  "Mapping.entries (Mapping.map_entry k f m) = (case Mapping.lookup m k of Some v \<Rightarrow> insert (k, f v) (Mapping.entries m - {(k, v)}) | None \<Rightarrow> Mapping.entries m)"
proof transfer
  fix m :: "'a \<Rightarrow> 'b option" and k f
  show "Map.graph (case m k of None \<Rightarrow> m | Some v \<Rightarrow> m(k \<mapsto> f v)) = (case m k of None \<Rightarrow> Map.graph m | Some v \<Rightarrow> insert (k, f v) (Map.graph m - {(k, v)}))"
  proof (cases "m k")
    case None
    then show ?thesis by (simp add: graph_def)
  next
    case (Some a)
    then show ?thesis
      (* TODO find a simpler proof *)
      apply (simp add: graph_def)
      apply safe
           apply simp_all
         apply presburger
        apply (metis option.inject)
       apply presburger
      apply (metis option.inject)
      done
  qed
qed

text\<open>
  Entries after @{const Mapping.map_default} are the original entries, possibly with the mapped
  entry replaced or the mapped default value inserted
\<close>
lemma entries_map_default:
  " Mapping.entries (Mapping.map_default k v f m) =
  ( case Mapping.lookup m k of
      Some v \<Rightarrow> insert (k, f v) (Mapping.entries m - {(k, v)})
    | None \<Rightarrow> insert (k, f v) (Mapping.entries m)
  )"
proof (cases "k \<in> Mapping.keys m")
  case True
  then show ?thesis
    unfolding map_default_def entries_map_entry entries_default
    using in_keysD by (fastforce simp add: lookup_default lookup_default_def)
next
  case False
  moreover have "Mapping.lookup m k = None"
    using False by (simp add: domIff keys_dom_lookup)
  ultimately show ?thesis
    unfolding map_default_def entries_map_entry entries_default
    using entries_keysD by (fastforce simp add: lookup_default lookup_default_def)
qed

text\<open>
  Prepending an element to a list value and then mapping a function over all elements of all values
  is the same as first mapping that function and then prepending an already mapped element
\<close>
lemma map_values_map_entry_Cons:
  " Mapping.map_values (\<lambda>k. map f) (Mapping.map_entry k ((#) a) m)
  = Mapping.map_entry k ((#) (f a)) (Mapping.map_values (\<lambda>k. map f) m)"
proof transfer
  fix m :: "'a \<Rightarrow> 'c list option" and f :: "'c \<Rightarrow> 'b" and k a
  show
    " (\<lambda>x. map_option (map f) ((case m k of None \<Rightarrow> m | Some v \<Rightarrow> m(k \<mapsto> a # v)) x))
    = ( case map_option (map f) (m k) of
          None \<Rightarrow> \<lambda>x. map_option (map f) (m x)
        | Some v \<Rightarrow> (\<lambda>x. map_option (map f) (m x))(k \<mapsto> f a # v))"
    by (cases "m k" ; fastforce)
qed

text\<open>
  Mapping formed from updated association list is the same as prepending the update to the list if
  the key is not yet present.
\<close>
lemma Mapping_AList_update_is_Cons:
  assumes "k \<notin> fst ` set xs"
    shows "Mapping (AList.update k v xs) = Mapping ((k, v) # xs)"
  using update_Some_unfold weak_map_of_SomeI
  by (subst equal_Mapping[unfolded equal])
     (fastforce simp add: dom_update update_Some_unfold)

text\<open>Mappings formed from lists of equal element sets with distinct keys are equal\<close>
lemma Mapping_eqI_distinct_keys:
  assumes "set xs = set ys"
      and "distinct (map fst xs)"
      and "distinct (map fst ys)"
    shows "Mapping xs = Mapping ys"
  using assms by (metis Mapping.abs_eq map_of_inject_set)

subsection\<open>Map or Default\<close>

text\<open>
  Mapping variant of @{const AList.map_default}

  Note that @{const AList.map_default} and @{const Mapping.map_default} are different!
  @{const Mapping.map_default} first inserts the default value if key is missing and then maps
  whatever is there.
  @{const AList.map_default} only inserts the default value if key is missing, otherwise maps the
  present value.
  Note how in the AList version we do not apply the map to the default value!
\<close>
definition map_or_default :: "'a \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping"
  where "map_or_default k v f m =
  ( if k \<in> Mapping.keys m
      then Mapping.map_entry k f m
      else Mapping.update k v m)"

lemma map_or_default_Mapping [code]:
  "map_or_default k v f (Mapping xs) = Mapping (AList.map_default k v f xs)"
  unfolding map_or_default_def
  by transfer (simp add: domIff map_of_map_default option.case_eq_if)

end