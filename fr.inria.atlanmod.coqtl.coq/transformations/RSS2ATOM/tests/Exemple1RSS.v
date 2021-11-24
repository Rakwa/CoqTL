(********************************************************************
	@name Coq declarations for model
	@date 2021/11/24 11:22:18
	@description Automatically generated by XMI2Coq transformation.
 ********************************************************************)
		 
Require Import List.
Require Import core.Model.
Require Import String.
Require Import transformations.RSS2ATOM.RSS.
Open Scope string_scope.


Definition Exemple1RSS : Model RSSMetamodel_Object RSSMetamodel_Link :=
	(Build_Model
		(
		(Build_RSSMetamodel_Object ChannelClass (BuildChannel  "Atoute.org"  (Some "http://www.atoute.org/") ""  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some 0)  (Some "")  (Some 0)  (Some "")  None   (Some ""))) :: 
		(Build_RSSMetamodel_Object RSSClass (BuildRSS  "0.91")) :: 
		(Build_RSSMetamodel_Object ItemClass (BuildItem  "Outils de recherche pour professionnels" "http://www.atoute.org/medecine_pro.htm" ""  None   (Some "")  (Some "")  (Some ""))) :: 
		(Build_RSSMetamodel_Object ItemClass (BuildItem  "La page du médecin" "http://www.atoute.org/page_du_medecin/spe/mg/mg_1024.htm" ""  None   (Some "")  (Some "")  (Some ""))) :: 
		(Build_RSSMetamodel_Object ItemClass (BuildItem  "Dictionnaires médicaux" "http://www.atoute.org/dictionnaire_medical.htm" ""  None   (Some "")  (Some "")  (Some ""))) :: 
		nil)
		(
		(Build_RSSMetamodel_Link ChannelRssReference (BuildChannelRss (BuildChannel  "Atoute.org"  (Some "http://www.atoute.org/") ""  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some 0)  (Some "")  (Some 0)  (Some "")  None   (Some "")) (BuildRSS  "0.91"))) ::
		(Build_RSSMetamodel_Link ChannelItemsReference (BuildChannelItems (BuildChannel  "Atoute.org"  (Some "http://www.atoute.org/") ""  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some 0)  (Some "")  (Some 0)  (Some "")  None   (Some "")) ((BuildItem  "La page du médecin" "http://www.atoute.org/page_du_medecin/spe/mg/mg_1024.htm" ""  None   (Some "")  (Some "")  (Some "")) :: (BuildItem  "Outils de recherche pour professionnels" "http://www.atoute.org/medecine_pro.htm" ""  None   (Some "")  (Some "")  (Some "")) :: (BuildItem  "Dictionnaires médicaux" "http://www.atoute.org/dictionnaire_medical.htm" ""  None   (Some "")  (Some "")  (Some "")) :: nil ))) ::
		(Build_RSSMetamodel_Link RSSChannelReference (BuildRSSChannel (BuildRSS  "0.91") (BuildChannel  "Atoute.org"  (Some "http://www.atoute.org/") ""  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some 0)  (Some "")  (Some 0)  (Some "")  None   (Some "")))) ::
		(Build_RSSMetamodel_Link ItemChannelReference (BuildItemChannel (BuildItem  "Outils de recherche pour professionnels" "http://www.atoute.org/medecine_pro.htm" ""  None   (Some "")  (Some "")  (Some "")) (BuildChannel  "Atoute.org"  (Some "http://www.atoute.org/") ""  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some 0)  (Some "")  (Some 0)  (Some "")  None   (Some "")))) ::
		(Build_RSSMetamodel_Link ItemChannelReference (BuildItemChannel (BuildItem  "La page du médecin" "http://www.atoute.org/page_du_medecin/spe/mg/mg_1024.htm" ""  None   (Some "")  (Some "")  (Some "")) (BuildChannel  "Atoute.org"  (Some "http://www.atoute.org/") ""  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some 0)  (Some "")  (Some 0)  (Some "")  None   (Some "")))) ::
		(Build_RSSMetamodel_Link ItemChannelReference (BuildItemChannel (BuildItem  "Dictionnaires médicaux" "http://www.atoute.org/dictionnaire_medical.htm" ""  None   (Some "")  (Some "")  (Some "")) (BuildChannel  "Atoute.org"  (Some "http://www.atoute.org/") ""  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some "")  (Some 0)  (Some "")  (Some 0)  (Some "")  None   (Some "")))) ::
		nil)
	).
