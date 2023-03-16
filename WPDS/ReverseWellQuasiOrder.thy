theory ReverseWellQuasiOrder
  imports "Well_Quasi_Orders.Well_Quasi_Orders" 
begin

class reverse_wqo = preorder +
  assumes good: "good (\<ge>) f"

lemma reverse_wqo_on_class [simp, intro]:
  "wqo_on (\<ge>) (UNIV :: ('a :: reverse_wqo) set)"
  using good by (auto simp: wqo_on_def transp_on_def almost_full_on_def dest: order_trans)

end