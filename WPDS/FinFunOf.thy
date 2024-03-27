theory FinFunOf imports FinFun.FinFun begin

unbundle finfun_syntax

definition assoc_list_on :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a * 'b) list" where
  "assoc_list_on l f = (map (\<lambda>x. (x, f x)) l)"

lemma assoc_list_on_app':
  assumes "x \<in> set l"
  shows "map_of (assoc_list_on l f) x = Some (f x)"
  using assms
  unfolding assoc_list_on_def by (induction l) auto

lemma assoc_list_on_app: "x \<in> set xs \<Longrightarrow> the (map_of (assoc_list_on xs f) x) = f x"
  by (induction xs) (auto simp add: assoc_list_on_app')

lemma assoc_list_on_dom: "dom (map_of (assoc_list_on xs f)) = set xs"
  unfolding assoc_list_on_def by (induction xs) force+

definition assoc_list_of :: "('a::enum \<Rightarrow> 'b) \<Rightarrow> ('a * 'b) list" where
  "assoc_list_of f = assoc_list_on enum_class.enum f"

lemma assoc_list_of_app': "map_of (assoc_list_of f) x = Some (f x)"
  unfolding assoc_list_of_def using assoc_list_on_app'[of x enum_class.enum f] 
  unfolding Enum.enum_class.enum_UNIV by auto

lemma assoc_list_of_app: "the (map_of (assoc_list_of f) x) = f x"
  unfolding assoc_list_of_def using assoc_list_on_app'[of x enum_class.enum f] 
  unfolding Enum.enum_class.enum_UNIV by auto

lemma assoc_list_of_dom: "dom (map_of (assoc_list_of f)) = UNIV"
  unfolding assoc_list_of_def using assoc_list_on_dom[of enum_class.enum f]
  unfolding Enum.enum_class.UNIV_enum by auto

lemma member_assoc_list_of_dom: "x \<in> dom (map_of (assoc_list_of f))"
  unfolding assoc_list_of_dom by auto

fun fin_fun_of_list :: "('a * 'b) list \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow>f 'b" where
  "fin_fun_of_list [] c = (K$ c)"
| "fin_fun_of_list ((a,b)#f) c = finfun_update_code (fin_fun_of_list f c) a b"

lemma fin_fun_of_list_app: "x \<in> dom (map_of l) \<Longrightarrow> (fin_fun_of_list l c) $ x = the ((map_of l) x)"
  by (induction l) (auto simp add: domIff)

lemma fin_fun_of_list_app': "x \<notin> dom (map_of l) \<Longrightarrow> (fin_fun_of_list l c) $ x = c"
  by (induction l) auto

definition fin_fun_of_fun :: "(('a::enum) \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow>f 'b" where
  "fin_fun_of_fun f = fin_fun_of_list (assoc_list_of f) (f (hd Enum.enum))"

lemma app_fin_fun_of_fun: "(fin_fun_of_fun f) $ x = f x"
  unfolding fin_fun_of_fun_def
  using fin_fun_of_list_app[of x "(assoc_list_of f)" " (f (hd enum_class.enum))", OF member_assoc_list_of_dom]
  using assoc_list_of_app by auto

end
