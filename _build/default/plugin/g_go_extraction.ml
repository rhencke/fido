
# 3 "plugin/g_go_extraction.mlg"
 

open Pp
open Names
open Libnames
open Stdarg
open Miniml
open Common
open Modutil
open Extract_env
open Go

(** Split a space-separated names string into a list of qualids. *)
let qualids_of_names names =
  names
  |> String.split_on_char ' '
  |> List.filter (fun s -> not (String.equal s ""))
  |> List.map (fun s -> qualid_of_ident (Id.of_string s))

(** Extract [qids] into [file_id.go] as a monolithic Go package. *)
let go_extract_file ~opaque_access file_id qids =
  let globals =
    List.map
      (fun qid ->
        { glob = Smartlocate.global_with_alias qid; inst = InfvInst.empty })
      qids
  in
  let state =
    State.make ~modular:false ~library:false ~keywords:Go.go_descr.keywords ()
  in
  let struc = mono_environment state ~opaque_access globals [] in
  let safe  = { mldummy = false; tdummy = false; tunknown = false; magic = false } in
  let base  = Id.to_string file_id in
  let name  = Id.of_string base in
  let fname = base ^ ".go" in
  let pp    =
    Go.go_descr.preamble state name None DirPath.Set.empty safe ++
    Go.go_descr.pp_struct state struc
  in
  let oc = open_out fname in
  output_string oc (Pp.string_of_ppcmds pp);
  close_out oc;
  Feedback.msg_notice (str "Extracted to " ++ str fname)

(** Extract [entry_qid] and all its dependencies into [file_id.go] as
    [package main], then append [func main() { _ = EntryFn() }]. *)
let go_extract_main ~opaque_access file_id entry_qid =
  let gr     = Smartlocate.global_with_alias entry_qid in
  let globals = [{ glob = gr; inst = InfvInst.empty }] in
  let state  =
    State.make ~modular:false ~library:false ~keywords:Go.go_descr.keywords ()
  in
  let struc  = mono_environment state ~opaque_access globals [] in
  let safe   = { mldummy = false; tdummy = false; tunknown = false; magic = false } in
  let base   = Id.to_string file_id in
  let name   = Id.of_string base in
  let fname  = base ^ ".go" in
  let entry_basename = Id.to_string (Nametab.basename_of_global gr) in
  (* Strip the entry Dterm from the structure and capture its body so we
     can inline it directly into func main() instead of calling by name. *)
  let entry_body = ref None in
  let filter_elem (lbl, elem) =
    match elem with
    | SEdecl (Dterm (r, body, _))
      when String.equal (Go.global_basename r) entry_basename ->
        entry_body := Some body; None
    | _ -> Some (lbl, elem)
  in
  let filtered_struc =
    List.map (fun (mp, sel) -> (mp, List.filter_map filter_elem sel)) struc
  in
  let pp =
    Go.preamble_for_pkg "main" state name None DirPath.Set.empty safe ++
    Go.go_descr.pp_struct state filtered_struc ++
    (match !entry_body with
     | Some body -> Go.pp_main_body state body
     | None      -> Go.pp_main_call entry_basename)
  in
  let oc = open_out fname in
  output_string oc (Pp.string_of_ppcmds pp);
  close_out oc;
  Feedback.msg_notice (str "Extracted to " ++ str fname)


# 88 "plugin/g_go_extraction.ml"

let () = Vernacextend.static_vernac_extend ~plugin:(Some "rocq-go-extraction") ~command:"GoFileExtraction" ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_query) ~ignore_kw:false ?entry:None 
         [(Vernacextend.TyML
         (false,
          Vernacextend.TyTerminal
          ("Go",
           Vernacextend.TyTerminal
           ("File",
            Vernacextend.TyTerminal
            ("Extraction",
             Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident),
             Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_string),
             Vernacextend.TyNil))))),
          (let coqpp_body file names () =
            Vernactypes.vtopaqueaccess (fun ~opaque_access -> (
# 92 "plugin/g_go_extraction.mlg"
       go_extract_file file (qualids_of_names names) 
# 106 "plugin/g_go_extraction.ml"
)
            ~opaque_access) in fun file names ?loc ~atts () ->
            coqpp_body file names (Attributes.unsupported_attributes atts)),
          None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "rocq-go-extraction") ~command:"GoMainExtraction" ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_query) ~ignore_kw:false ?entry:None 
         [(Vernacextend.TyML
         (false,
          Vernacextend.TyTerminal
          ("Go",
           Vernacextend.TyTerminal
           ("Main",
            Vernacextend.TyTerminal
            ("Extraction",
             Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident),
             Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_string),
             Vernacextend.TyNil))))),
          (let coqpp_body file name () =
            Vernactypes.vtopaqueaccess (fun ~opaque_access -> (
# 100 "plugin/g_go_extraction.mlg"
      
    let qid = qualid_of_ident (Id.of_string name) in
    go_extract_main file qid
  
# 131 "plugin/g_go_extraction.ml"
)
            ~opaque_access) in fun file name ?loc ~atts () ->
            coqpp_body file name (Attributes.unsupported_attributes atts)),
          None))]

