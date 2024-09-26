let _ = Mltop.add_known_module "coq-metaprogramming.derivemap.plugin"

# 3 "derive-map/ocaml/src/g_derivemap.mlg"
  
  open Stdarg


let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-metaprogramming.derivemap.plugin") ~command:"DeriveMap" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("DeriveMap", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ref), 
                                     Vernacextend.TyNil)), (let coqpp_body ind
                                                           () = Vernactypes.vtdefault (fun () -> 
                                                                
# 9 "derive-map/ocaml/src/g_derivemap.mlg"
                                Derivemap.derive ind 
                                                                ) in fun ind
                                                           ?loc ~atts ()
                                                           -> coqpp_body ind
                                                           (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-metaprogramming.derivemap.plugin") ~command:"TestCommand" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("TestCommand", 
                                     Vernacextend.TyNil), (let coqpp_body () = 
                                                          Vernactypes.vtdefault (fun () -> 
                                                          
# 13 "derive-map/ocaml/src/g_derivemap.mlg"
                         Feedback.msg_notice (Pp.str "Hello from the plugin") 
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

