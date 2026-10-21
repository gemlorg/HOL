(* this is an -*- sml -*- file *)
val _ = use "poly/poly-init.ML";

val _ = use "../tools/parsing/AttributeSyntax.sig";
val _ = use "../tools/parsing/AttributeSyntax.sml";
val _ = use "../tools/parsing/HolLex.sml";
val _ = use "../tools/util/SimpleBuffer.sig";
val _ = use "../tools/util/SimpleBuffer.sml";
val _ = use "../tools/Holmake/hfs/HOLFS_dtype.sml";
val _ = use "../tools/Holmake/hfs/HFS_NameMunge.sig";
val _ = use "../tools/Holmake/poly/HFS_NameMunge.sml";
val _ = use "../tools/Holmake/hfs/HOLFileSys.sig";
val _ = use "../tools/Holmake/hfs/HOLFileSys.sml";
val _ = use "../tools/parsing/HOLSourceAST.sig";
val _ = use "../tools/parsing/HOLSourceAST.sml";
val _ = use "../tools/parsing/HOLSourceParser.sig";
val _ = use "../tools/parsing/HOLSourceParser.sml";
val _ = use "../tools/parsing/HOLSourceExpand.sig";
val _ = use "../tools/parsing/HOLSourceExpand.sml";
val _ = use "../tools/parsing/HOLSourcePrinter.sig";
val _ = use "../tools/parsing/HOLSourcePrinter.sml";
val _ = use "../tools/parsing/HOLSource.sig";
val _ = use "../tools/parsing/HOLSource.sml";
(* Reads what HOLSourceParser produces and nothing from the kernel, so
   it belongs in the executable rather than in sigobj, where `hol lsp'
   had to `Meta.load' it at every server start. *)
val _ = use "../tools/parsing/TacticParse.sig";
val _ = use "../tools/parsing/TacticParse.sml";
val _ = use "../tools/parsing/ProofStepPlan.sig";
val _ = use "../tools/parsing/ProofStepPlan.sml";
val _ = use "poly/sref-bootstrap.ML";

val _ = use "../src/portableML/UniversalType.sig";
val _ = use "../src/portableML/UniversalType.sml";
val _ = use "../src/portableML/poly/PrettyImpl.sml";
val _ = use "lsp/LSPExtension.sig";
val _ = use "lsp/LSPExtension.sml";
val _ = use "poly/quse.sig";
val _ = use "poly/quse.sml";

local

  val quiet_load = ref false;
  fun maybeWriteStderr s =
    if !quiet_load then () else
    (TextIO.output(TextIO.stdErr, s ^ "\n");
     TextIO.flushOut TextIO.stdErr);

  fun die s = (maybeWriteStderr s; raise Fail s)

  fun warn s = maybeWriteStderr ("WARNING: " ^ s)

  val meta_debug = ref false

  fun MDBG s = if !meta_debug then
                 TextIO.print("META_DEBUG: " ^ s() ^ "\n")
               else ()

  infix ++
  fun p1 ++ p2 = OS.Path.concat (p1, p2)
  open Systeml

structure HFS = HOLFileSys

val loadpathdb =
    ref (Binarymap.mkDict String.compare : (string,string) Binarymap.dict)

fun quse s = let
  val _ = if HFS.access (s, [HFS.A_READ]) then ()
          else die ("Use: non-existent file "^s)
  val _ = MDBG (fn _ => "Call quse " ^ s)
  val full = OS.Path.mkCanonical
               (OS.Path.mkAbsolute{path = s, relativeTo = HFS.getDir()})
in
  QUse.use s ;
  loadpathdb := Binarymap.insert(!loadpathdb,OS.Path.file full,OS.Path.dir full)
end handle
    OS.Path.Path => die ("Path exception in quse "^s)
  | e => (
    maybeWriteStderr("error in quse " ^ s ^ " : " ^ General.exnMessage e);
    PolyML.Exception.reraise e)

fun myuse f =
  let val op ++ = OS.Path.concat
      val file = OS.Path.file f
      val pd = !PolyML.Compiler.printDepth
  in
    PolyML.print_depth 0;
    (quse f handle e => (PolyML.print_depth pd; PolyML.Exception.reraise e));
    PolyML.print_depth pd
  end handle OS.Path.Path => die ("Path exception in myuse "^f)

val loadPath : string list ref = ref [OS.Path.concat(HOLDIR, "sigobj")];

val loadedMods = ref (Binaryset.empty String.compare);
val _ = loadedMods := Binaryset.addList (!loadedMods, [
  "Real", "Int", "List", "Binaryset", "Binarymap", "Listsort",
  "Array", "Array2", "Vector", "UniversalType", "DArray", "DString",
  "HOLSourceAST", "HOLSourceParser", "HOLSourceExpand", "HOLSourcePrinter",
  "HOLSource", "TacticParse", "ProofStepPlan",
  "Systeml", "PrettyImpl", "LSPExtension", "SHA1"])

fun findUo modPath [] = NONE
  | findUo modPath (search::rest) =
      let val path =
         OS.Path.mkAbsolute
           {path = modPath,
            relativeTo = OS.Path.mkAbsolute
                           {path=search, relativeTo = HFS.getDir ()}};
      in
        if HFS.access (path, []) then
          SOME path
        else
          findUo modPath rest
      end;

val _ = holpathdb.extend_db {vname = "HOLDIR", path = Systeml.HOLDIR}

fun checkLoadCase modName files =
  let
    val lc = String.map Char.toLower
    val lcModName = lc modName
    fun srcBase f = OS.Path.base (OS.Path.file f)
    fun mismatch f =
      let val b = srcBase f
      in b <> modName andalso lc b = lcModName end
  in
    case List.find mismatch files of
        NONE => ()
      | SOME f =>
          die ("load: requested \"" ^ modName ^
               "\" but module is registered as \"" ^ srcBase f ^ "\"")
  end

(* A module's manifest: the modules its .ui and .uo files list, and the
   .sig and .sml files they list, in the order listed. *)
fun readManifest ps modPath =
  let
    val modName = OS.Path.file modPath
    fun str f = ">" ^ f ^ "< -- " ^ String.concatWith " -- " ps
    fun read ext =
      case findUo (modPath ^ ext) ("."::(!loadPath)) of
          NONE => die ("Cannot find file " ^ modPath ^ ext)
        | SOME uo =>
          let
            val i = HFS.openIn uo
            val files =
                String.tokens (fn c => c = #"\n") (HFS.inputAll i)
            val _ = HFS.closeIn i
            val _ = checkLoadCase modName files
            fun isSource f =
                case OS.Path.ext f of
                    SOME "sml" => true
                  | SOME "sig" => true
                  | _ => false
                handle OS.Path.InvalidArc =>
                         die ("Invalid arc exception in loading "^str f)
                     | OS.Path.Path => die ("Path exception in loading "^str f)
            val (srcs, deps) = List.partition isSource files
          in
            (map (fn d => (uo::ps, holpathdb.subst_pathvars d)) deps, srcs)
          end
    val (uideps, uisrcs) = read ".ui"
    val (uodeps, uosrcs) = read ".uo"
  in
    {deps = uideps @ uodeps, srcs = uisrcs @ uosrcs}
  end
  handle e => (
    maybeWriteStderr ("error in load " ^ modPath ^ " : " ^
                      General.exnMessage e);
    PolyML.Exception.reraise e)

(* Loads modPath and the modules it depends on that are not yet loaded.
   Each step loads, of the modules whose dependencies are all loaded, the
   one whose name is least.  So a set of modules always loads in the same
   order, and restricted to the ancestors of any module in it, that order
   is the order loading that module alone gives.  The order matters
   because loading a theory registers things (cv_trans translations,
   compset entries, overloads) where the last registration wins. *)
fun load ps use modPath =
  let
    val _ = MDBG (fn _ => "Call load " ^ modPath)
    fun loaded m = Binaryset.member (!loadedMods, m)
    (* the manifests of every module still to load, by module name *)
    fun collect (plan, []) = plan
      | collect (plan, (ps, path) :: rest) =
        let val m = OS.Path.file path
        in
          if loaded m orelse isSome (Binarymap.peek (plan, m)) then
            collect (plan, rest)
          else
            let val {deps, srcs} = readManifest ps path
            in
              collect (Binarymap.insert (plan, m, (deps, srcs)), deps @ rest)
            end
        end
    val plan = collect (Binarymap.mkDict String.compare,
                        [(ps, holpathdb.subst_pathvars modPath)])
    fun planned d = isSome (Binarymap.peek (plan, d))
    (* A module without a .sig lists itself in its .uo. *)
    fun depNames m deps =
        Binaryset.listItems
          (Binaryset.addList
             (Binaryset.empty String.compare,
              List.filter (fn d => d <> m andalso planned d)
                          (map (OS.Path.file o #2) deps)))
    (* for each module, how many of its dependencies are still to load,
       and which modules depend on it *)
    val (waiting, dependents) =
        Binarymap.foldl
          (fn (m, (deps, _), (w, ds)) =>
              let val dns = depNames m deps
                  fun addDependent (d, ds) =
                      Binarymap.insert
                        (ds, d, m :: getOpt (Binarymap.peek (ds, d), []))
              in
                (Binarymap.insert (w, m, length dns),
                 List.foldl addDependent ds dns)
              end)
          (Binarymap.mkDict String.compare, Binarymap.mkDict String.compare)
          plan
    fun least s = Binaryset.foldr (fn (x, _) => SOME x) NONE s
    fun useSrc f =
        use f handle OS.SysErr (msg, _) =>
                     die ("System error '" ^ msg ^ "' in loading " ^ f)
    fun step (waiting, ready) =
        case least ready of
            SOME m =>
            let
              val _ = List.app useSrc (#2 (Binarymap.find (plan, m)))
              val _ = loadedMods := Binaryset.add (!loadedMods, m)
              fun release (d, (w, r)) =
                  let val n = Binarymap.find (w, d) - 1
                  in
                    (Binarymap.insert (w, d, n),
                     if n = 0 then Binaryset.add (r, d) else r)
                  end
            in
              step (List.foldl release
                      (waiting, Binaryset.delete (ready, m))
                      (getOpt (Binarymap.peek (dependents, m), [])))
            end
          | NONE =>
            case List.filter (not o loaded) (map #1 (Binarymap.listItems plan))
             of [] => ()
              | stuck => die ("Dependency cycle among " ^
                              String.concatWith ", " stuck)
    val ready =
        Binarymap.foldl (fn (m, 0, r) => Binaryset.add (r, m) | (_, _, r) => r)
                        (Binaryset.empty String.compare) waiting
  in
    step (waiting, ready)
  end handle e => (
    maybeWriteStderr("error in load " ^ modPath ^ " : " ^ General.exnMessage e);
    PolyML.Exception.reraise e)
in

  structure Meta = struct
    val meta_debug = meta_debug
    val quiet_load = quiet_load
    val loadPlan = load []
    val qquse = myuse o holpathdb.subst_pathvars
    val load = loadPlan qquse
    fun qload s = let
      val x = !quiet_load
      in quiet_load := true; load s; quiet_load := x end
    val loadPath = loadPath;
    fun loaded () = Binaryset.listItems (!loadedMods);
    fun fakeload s =
        loadedMods := Binaryset.add(!loadedMods,s)
    (* Snapshot / restore of the load-tracking set.  Used by the LSP
       to keep loadedMods in sync with Context: on Context.restore
       ancestor theory data disappears from the graph, so their entries
       must also come out of loadedMods or subsequent `load`s see them
       as already-loaded and skip re-populating the graph.  *)
    fun snapshotLoaded () = let val s = !loadedMods
                            in fn () => loadedMods := s end
    fun findMod modname = findUo (modname ^ ".uo") ("." :: !loadPath)
    fun fileDirMap () = !loadpathdb
  end;

open Meta;

end;


structure PolyWord8 = Word8;
(* awfulness to make the environment look like Moscow ML's *)

(* In Poly/ML "before" is 'a * 'b -> 'a and General.before is 'a * unit -> 'a.
   The Basis library says both should be 'a * unit -> 'a, but in Moscow ML,
   before is 'a * 'b -> 'a too.  Ick. *)

structure Word8 = struct
  open PolyWord8;
  fun toLargeWord w =
    Word.fromLargeWord (PolyWord8.toLargeWord w);
end;

structure Path = OS.Path;
structure Process = OS.Process;
structure FileSys = HOLFileSys;

exception Interrupt = SML90.Interrupt;
exception Io = IO.Io;
exception SysErr = OS.SysErr;

val polyInitStatus = 2;
