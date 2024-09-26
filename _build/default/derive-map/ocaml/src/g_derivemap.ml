let _ = Mltop.add_known_module "derivemap-plugin.plugin"

# 3 "derive-map/ocaml/src/g_derivemap.mlg"
  
  (*open Derivemap*)
  open Stdarg


let () = Vernacextend.static_vernac_extend ~plugin:(Some "derivemap-plugin.plugin") ~command:"DeriveMap" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("DeriveMap", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ref), 
                                     Vernacextend.TyNil)), (let coqpp_body ind
                                                           () = Vernactypes.vtdefault (fun () -> 
                                                                
# 10 "derive-map/ocaml/src/g_derivemap.mlg"
                                Derivemap.derive ind 
                                                                ) in fun ind
                                                           ?loc ~atts ()
                                                           -> coqpp_body ind
                                                           (Attributes.unsupported_attributes atts)), None))]

