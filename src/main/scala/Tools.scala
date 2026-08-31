package morkl

/** ==============================================================================================
 *  EXTERNAL TOOL RESOLUTION — one policy, one implementation, no absolute paths in the tree.
 *
 *  The provers and the e-graph engine are found the same way everywhere (Scala, `sh`, Python):
 *
 *    1. the explicit environment override — `Z3`, `VAMPIRE`, `EGGLOG` — which may name an
 *       executable on `PATH` or an absolute path;
 *    2. `PATH`;
 *    3. a short list of CONVENTIONAL install locations for that tool, tried in order;
 *    4. otherwise ABSENT — and every caller says so out loud rather than silently degrading
 *       (`docs/traps.md` §3: a semantics-critical path must never quietly become a no-op).
 *
 *  The `sh` twin is `scripts/toolpath.sh` and the Python twin is `scripts/toolpath.py`; all three
 *  read the same environment variables and the same conventional-location lists, so a machine
 *  configured for one is configured for all.
 *  ============================================================================================== */
object Tools:
  import java.io.File

  /** one external tool: the binary name, its env override, and where it conventionally lives */
  final case class Tool(name: String, envVar: String, conventional: List[String]):
    /** the resolved executable, or `None`.  Probed once per JVM. */
    lazy val path: Option[String] = Tools.locate(this)
    def isAvailable: Boolean = path.isDefined
    /** the resolved executable, or a diagnostic that names the override */
    def require(): String = path.getOrElse(throw new IllegalStateException(missing))
    def missing: String =
      s"$name not found: set $$$envVar to its path, or put `$name` on PATH " +
      s"(also tried: ${conventional.mkString(", ")})"

  private def home: String = System.getProperty("user.home")

  val z3: Tool = Tool("z3", "Z3",
    List("/usr/local/bin/z3", "/opt/homebrew/bin/z3", s"$home/.local/bin/z3"))
  val vampire: Tool = Tool("vampire", "VAMPIRE",
    List("/usr/local/bin/vampire", "/opt/homebrew/bin/vampire", s"$home/.local/bin/vampire"))
  val egglog: Tool = Tool("egglog", "EGGLOG",
    List(s"$home/.cargo/bin/egglog", "/usr/local/bin/egglog", "/opt/homebrew/bin/egglog"))

  val all: List[Tool] = List(z3, vampire, egglog)

  /** step 1-3 of the policy above. */
  private def locate(t: Tool): Option[String] =
    def runs(cmd: String): Boolean =
      try
        val p = new ProcessBuilder(cmd, versionFlag(t)).redirectErrorStream(true).start()
        p.getInputStream.readAllBytes()          // drain, or the child can block on a full pipe
        p.waitFor(); true                        // an exit code of any value means it EXECUTED
      catch case _: Throwable => false
    val fromEnv = sys.env.get(t.envVar).map(_.trim).filter(_.nonEmpty)
    val candidates =
      fromEnv.toList ++ List(t.name) ++ t.conventional      // bare name = the PATH lookup
    candidates.iterator
      .filter(c => !c.contains(File.separator) || new File(c).canExecute)
      .find(runs)

  /** the flag that makes the tool print something and exit without reading a problem file */
  private def versionFlag(t: Tool): String = t.name match
    case "vampire" => "--version"
    case "egglog" => "--version"
    case _ => "-version"

  /** a one-line report of what is and is not available — printed by the suites that need a tool,
   *  so a skipped obligation is visible instead of implied. */
  def report: String =
    all.map(t => s"${t.name}=${t.path.getOrElse("ABSENT")}").mkString("  ")
end Tools
