theory LTS imports Transition_Systems_and_Automata.Transition_System_Construction begin

type_synonym ('state, 'label) transition = "'state * 'label * 'state"

locale LTS =
  fixes transition_relation :: "('state, 'label) transition set"
    and r :: 'state
begin

fun execute :: "('state, 'label) transition \<Rightarrow> 'state \<Rightarrow> 'state" where 
  "execute (s, l, s') s'' = s'"

fun enabled :: "('state, 'label) transition \<Rightarrow> 'state \<Rightarrow> bool" where
  "enabled (s, l, s') s'' \<longleftrightarrow> (s, l, s') \<in> transition_relation \<and> s = s''"

interpretation transition_system execute enabled .



end

end