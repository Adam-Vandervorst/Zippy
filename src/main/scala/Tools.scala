package morkl

/** ==============================================================================================
 *  EXTERNAL TOOL RESOLUTION — one policy, three thin adapters, no absolute path anywhere.
 *
 *  `toolchain.conf` at the repo root IS the policy.  This file, `scripts/toolpath.sh` and
 *  `scripts/toolpath.py` all READ it: none of the three contains a tool name, an environment
 *  variable name, or an install location of its own, so there are no "twins" to drift apart and no
 *  generated file to go stale.
 *
 *  Resolution steps, in the order `toolchain.conf`'s `search` key gives:
 *
 *    `env`          the tool's declared environment override (`Z3`, `VAMPIRE`, `EGGLOG`), which may
 *                   be an absolute path or a bare name looked up on `PATH`;
 *    `zippy-tools`  `$ZIPPY_TOOLS/<binary>` — the ONE place a machine says where it keeps provers
 *                   that are not on `PATH`.  This replaced the former hardcoded
 *                   `/usr/local/bin`, `/opt/homebrew/bin`, `~/.local/bin`, `~/.cargo/bin` lists;
 *    `path`         `PATH`;
 *    `elan`         `$ELAN_HOME/bin/<binary>`, else `~/.elan/bin/<binary>` — elan's own root, from
 *                   its DOCUMENTED override and its DOCUMENTED default.  This step exists for
 *                   `lake` and only for `lake`: it is a toolchain SHIM that dispatches on the
 *                   `lean-toolchain` file beside the package, so a copy of it under `$ZIPPY_TOOLS`
 *                   would break the dispatch.  It is LAST, so `$LAKE` or a `PATH` entry always wins.
 *                   See `toolchain.conf`'s header.
 *
 *  Otherwise ABSENT — and every caller says so out loud rather than silently degrading
 *  (`docs/traps.md` §3: a semantics-critical path must never quietly become a no-op).
 *
 *  With `toolchain.conf` missing (or `$ZIPPY_TOOLCHAIN` pointing elsewhere) the policy degrades to
 *  `env, path` for a tool whose binary and env var follow the default naming — i.e. to the two
 *  LOCATION-FREE steps, never to a compiled-in path.
 *  ============================================================================================== */
object Tools:
  import java.io.File
  import java.nio.file.{Files, Path as JPath, Paths}

  /** one external tool, exactly as `toolchain.conf` declares it */
  final case class Tool(name: String, binary: String, envVar: String, versionFlag: String):
    /** the resolved executable, or `None`.  Probed once per JVM. */
    lazy val path: Option[String] = Tools.locate(this)
    def isAvailable: Boolean = path.isDefined
    /** the resolved executable, or a diagnostic that names every way to supply it */
    def require(): String = path.getOrElse(throw new IllegalStateException(missing))
    def missing: String =
      s"$name not found: set $$$envVar to its path, put `$binary` on PATH, or point $$ZIPPY_TOOLS " +
      s"at the directory holding it (policy: ${policyFile.map(_.getFileName.toString).getOrElse("toolchain.conf (ABSENT)")}, " +
      s"search order: ${search.mkString(", ")})"

  // ---------------------------------------------------------------------------------------------
  // the policy file
  // ---------------------------------------------------------------------------------------------
  private val defaultSearch = List("env", "path")   // the location-free fallback

  /** `$ZIPPY_TOOLCHAIN`, else the nearest `toolchain.conf` at or above the working directory. */
  private lazy val policyFile: Option[JPath] =
    sys.env.get("ZIPPY_TOOLCHAIN").map(_.trim).filter(_.nonEmpty).map(Paths.get(_))
      .filter(Files.isReadable)
      .orElse {
        Iterator.iterate(Paths.get("").toAbsolutePath.normalize)(_.getParent)
          .takeWhile(_ != null).map(_.resolve("toolchain.conf")).find(Files.isReadable)
      }

  /** (search order, tool name → declared keys).  A three-line ini reader; no dependency. */
  private lazy val policy: (List[String], Map[String, Map[String, String]]) =
    policyFile.map { f =>
      var order = defaultSearch
      val tools = scala.collection.mutable.LinkedHashMap.empty[String, Map[String, String]]
      var cur: Option[String] = None
      for raw <- scala.io.Source.fromFile(f.toFile).getLines() do
        val line = raw.takeWhile(_ != '#').trim
        if line.isEmpty then ()
        else if line.startsWith("[") && line.endsWith("]") then
          cur = Some(line.drop(1).dropRight(1).trim); tools.getOrElseUpdate(cur.get, Map.empty)
        else line.split("=", 2) match
          case Array(k, v) =>
            val (key, value) = (k.trim, v.trim)
            cur match
              case None => if key == "search" then order = value.split(",").map(_.trim).filter(_.nonEmpty).toList
              case Some(t) => tools(t) = tools(t) + (key -> value)
          case _ => ()
      (order, tools.toMap)
    }.getOrElse((defaultSearch, Map.empty))

  def search: List[String] = policy._1

  /** the tool named `n`, with the documented defaults for anything the policy leaves out */
  def tool(n: String): Tool =
    val d = policy._2.getOrElse(n, Map.empty)
    Tool(n, d.getOrElse("binary", n), d.getOrElse("env", n.toUpperCase), d.getOrElse("version-flag", "-version"))

  /** every tool the policy declares, in file order (the three below when it is absent) */
  lazy val all: List[Tool] =
    (if policy._2.nonEmpty then policy._2.keys.toList else List("z3", "vampire", "egglog")).map(tool)

  lazy val z3: Tool = tool("z3")
  lazy val vampire: Tool = tool("vampire")
  lazy val egglog: Tool = tool("egglog")

  // ---------------------------------------------------------------------------------------------
  // resolution
  // ---------------------------------------------------------------------------------------------
  private def locate(t: Tool): Option[String] =
    def runs(cmd: String): Boolean =
      try
        val p = new ProcessBuilder(cmd, t.versionFlag).redirectErrorStream(true).start()
        p.getInputStream.readAllBytes()          // drain, or the child can block on a full pipe
        p.waitFor(); true                        // an exit code of any value means it EXECUTED
      catch case _: Throwable => false
    def executable(c: String): Boolean = !c.contains(File.separator) || new File(c).canExecute
    search.iterator.flatMap {
      case "env" =>
        sys.env.get(t.envVar).map(_.trim).filter(_.nonEmpty).iterator
      case "zippy-tools" =>
        sys.env.get("ZIPPY_TOOLS").map(_.trim).filter(_.nonEmpty)
          .map(r => new File(expandHome(r), t.binary).getPath).iterator
      case "path" => Iterator(t.binary)          // bare name = the PATH lookup
      case "elan" =>
        Iterator(new File(new File(sys.env.get("ELAN_HOME").map(_.trim).filter(_.nonEmpty)
                                     .getOrElse(expandHome("~/.elan")), "bin"), t.binary).getPath)
      case _ => Iterator.empty
    }.filter(executable).find(runs)

  private def expandHome(s: String): String =
    if s == "~" || s.startsWith("~/") then System.getProperty("user.home") + s.drop(1) else s

  /** a one-line report of what is and is not available — printed by the suites that need a tool,
   *  so a skipped obligation is visible instead of implied. */
  def report: String =
    all.map(t => s"${t.name}=${t.path.getOrElse("ABSENT")}").mkString("  ")
end Tools
