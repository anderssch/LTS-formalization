theory FinFunOf imports FinFun.FinFun begin

unbundle finfun_syntax

fun fin_fun_of_list :: "('a * 'b) list \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow>f 'b" where
  "fin_fun_of_list [] c = (K$ c)"
| "fin_fun_of_list ((a,b)#f) c = finfun_update_code (fin_fun_of_list f c) a b"

lemma fin_fun_of_list_app: "x \<in> dom (map_of l) \<Longrightarrow> (fin_fun_of_list l c) $ x = the ((map_of l) x)"
  by (induction l) (auto simp add: domIff)

lemma fin_fun_of_list_app': "x \<notin> dom (map_of l) \<Longrightarrow> (fin_fun_of_list l c) $ x = c"
  by (induction l) auto

definition fin_fun_of_fun :: "(('a::enum) \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow>f 'b" where
  "fin_fun_of_fun f = fin_fun_of_list (map (\<lambda>x. (x, f x)) Enum.enum) (f (hd Enum.enum))"

lemma x'':
  assumes "x \<in> set l"
  shows "map_of (map (\<lambda>x. (x, f x)) l) x = Some (f x)"
  using assms
  apply (induction l)
   apply auto
  done

lemma x': "dom (map_of (map (\<lambda>x. (x, f x)) enum_class.enum)) = UNIV"
  apply auto
  subgoal for x
    apply (rule exI[of _  "f x"])
    using x''[of x enum_class.enum f]
    unfolding Enum.enum_class.enum_UNIV apply auto
    done
  done

lemma x: "x \<in> dom (map_of (map (\<lambda>x. (x, f x)) enum_class.enum))"
  unfolding x' by auto

lemma fin_fun_of_fun: "(fin_fun_of_fun f) $ x = f x"
  unfolding fin_fun_of_fun_def
  using fin_fun_of_list_app[of x "(map (\<lambda>x. (x, f x)) Enum.enum)", OF x]
  using x
  by (smt (verit, del_insts) domD ex_map_conv fin_fun_of_list_app' fst_conv map_of_SomeD option.sel
      snd_conv)

end