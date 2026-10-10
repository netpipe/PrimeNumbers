/* =========================================================================
 * primecheck.cpp — single-file Qt 5.12 primality checker (GUI + CLI hybrid)
 *
 * Build with qmake — primecheck.pro:
 *     QT       += widgets
 *     CONFIG   += c++11
 *     TARGET    = primecheck
 *     SOURCES  += main.cpp
 *   then:  qmake && make
 *
 * Or manually on Linux:
 *     g++ -fPIC -std=c++11 main.cpp -o primecheck \
 *         $(pkg-config --cflags --libs Qt5Widgets)
 *
 * Usage:
 *     ./primecheck                        → GUI (no arguments)
 *     ./primecheck 1000000007             → CLI verdict
 *     ./primecheck -v --selftest          → verbose / known-answer tests
 *     ./primecheck --gui 7919             → GUI with number prefilled
 *     ./primecheck --help                 → full CLI documentation
 * ========================================================================= */

#include <QApplication>
#include <QComboBox>
#include <QCoreApplication>
#include <QElapsedTimer>
#include <QGroupBox>
#include <QHBoxLayout>
#include <QLabel>
#include <QLineEdit>
#include <QListWidget>
#include <QLocale>
#include <QPushButton>
#include <QRandomGenerator>
#include <QSpinBox>
#include <QTextStream>
#include <QTime>
#include <QVBoxLayout>
#include <QWidget>

#include <vector>

/* =========================================================================
 *  CORE MATH
 * ========================================================================= */

static const quint64 TRIAL_LIMIT = 100000;                    // stage-1 sieve bound
static const quint64 TRIAL_FULL  = TRIAL_LIMIT * TRIAL_LIMIT; // n < 10^10 fully decidable by trial

enum class Mode { Auto = 0, TrialOnly = 1, MillerRabinOnly = 2, Fermat = 3 };

struct Report
{
    quint64 n = 0;
    bool prime = false;
    bool certain = true;        // false only for Fermat "probably prime"
    bool defined = true;        // false for n < 2
    bool inconclusive = false;  // trial-only mode past its cap
    QString method;
    QStringList trace;
    quint64 factor = 0;         // smallest factor, if found
    quint64 witness = 0;        // Miller-Rabin / Fermat witness base
    qint64 micros = 0;
};

static quint64 gcd64(quint64 a, quint64 b)
{
    while (b) { const quint64 t = a % b; a = b; b = t; }
    return a;
}

// (a + b) mod m without overflow, requires a,b < m
static inline quint64 addmod(quint64 a, quint64 b, quint64 m)
{
    return (a >= m - b) ? (a - (m - b)) : (a + b);
}

// (a * b) mod m without overflow
static inline quint64 mulmod(quint64 a, quint64 b, quint64 m)
{
#if defined(__SIZEOF_INT128__)
    return (quint64)(((unsigned __int128)(a % m) * (b % m)) % m);
#else
    // Portable fallback (MSVC): double-and-add, O(64) per multiply
    quint64 r = 0;
    a %= m;
    while (b) {
        if (b & 1) r = addmod(r, a, m);
        b >>= 1;
        if (b) a = addmod(a, a, m);
    }
    return r;
#endif
}

static quint64 powmod(quint64 base, quint64 exp, quint64 mod)
{
    quint64 r = 1 % mod;
    base %= mod;
    while (exp) {
        if (exp & 1) r = mulmod(r, base, mod);
        exp >>= 1;
        if (exp) base = mulmod(base, base, mod);
    }
    return r;
}

static std::vector<quint64> primesUpTo(quint64 limit)
{
    std::vector<quint64> out;
    if (limit < 2) return out;
    std::vector<char> composite(limit + 1, 0);
    for (quint64 i = 2; i <= limit; ++i) {
        if (composite[i]) continue;
        out.push_back(i);
        if (i <= limit / i)
            for (quint64 j = i * i; j <= limit; j += i)
                composite[j] = 1;
    }
    return out;
}

static const std::vector<quint64> &smallPrimes()
{
    static const std::vector<quint64> primes = primesUpTo(TRIAL_LIMIT);
    return primes;
}

// Stage 1 — trial division by the pre-sieved primes.
// returns  1 = proved prime, -1 = composite (factor set), 0 = inconclusive
static int trialStage(quint64 n, quint64 &factor, qint64 &divisions)
{
    const std::vector<quint64> &primes = smallPrimes();
    divisions = 0;
    for (size_t i = 0; i < primes.size(); ++i) {
        const quint64 p = primes[i];
        if (p > n / p) return 1;           // passed sqrt(n): no factor exists → prime
        ++divisions;
        if (n % p == 0) { factor = p; return -1; }
    }
    return 0;                              // primes exhausted before sqrt(n)
}

// One strong probable-prime round of Miller-Rabin
static bool mrPass(quint64 a, quint64 n, quint64 d, int s)
{
    quint64 x = powmod(a, d, n);
    if (x == 1 || x == n - 1) return true;
    for (int r = 1; r < s; ++r) {
        x = mulmod(x, x, n);
        if (x == n - 1) return true;
    }
    return false;
}

// Stage 2 — deterministic Miller-Rabin
static void runMillerRabin(Report &rep)
{
    const quint64 n = rep.n;
    quint64 d = n - 1;
    int s = 0;
    while ((d & 1) == 0) { d >>= 1; ++s; }
    rep.trace << QString("Stage 2  Miller-Rabin: n - 1 = %1 * 2^%2.").arg(d).arg(s);

    // First 12 prime bases. Proven deterministic for every
    // n < 3,317,044,064,679,887,385,961,981 (~3.3e24), which comfortably
    // covers the entire 64-bit range (max ~1.8e19). No probability involved.
    static const quint64 bases[] = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37 };

    for (size_t i = 0; i < sizeof(bases) / sizeof(bases[0]); ++i) {
        const quint64 a = bases[i];
        if (a % n == 0) continue;
        if (!mrPass(a, n, d, s)) {
            rep.witness = a;
            rep.method = QString("deterministic Miller-Rabin — base %1 is a compositeness witness").arg(a);
            rep.trace << QString("         base %1 FAILED the strong test → n is certainly composite.").arg(a);
            return;
        }
        rep.trace << QString("         base %1 passed.").arg(a);
    }
    rep.prime = true;
    rep.method = QStringLiteral("deterministic Miller-Rabin — all 12 prime bases passed");
    rep.trace << QStringLiteral("         Bases 2,3,5,...,37 all passed → n is certainly prime (not probabilistic).");
}

// Optional Fermat mode (educational): a^(n-1) = 1 (mod n)
static void runFermat(Report &rep, int rounds)
{
    const quint64 n = rep.n;
    if (n == 2 || n == 3) {
        rep.prime = true;
        rep.method = QStringLiteral("small prime lookup");
        return;
    }
    if ((n & 1) == 0) {
        rep.factor = 2;
        rep.method = QStringLiteral("even-number shortcut");
        rep.trace << QString("n is even and n > 2: n = 2 * %1.").arg(n / 2);
        return;
    }
    rep.trace << QString("Fermat test (%1 rounds): for random a, check gcd(a,n)=1 and a^(n-1) = 1 (mod n).").arg(rounds);
    for (int i = 1; i <= rounds; ++i) {
        const quint64 a = 2 + QRandomGenerator::global()->generate64() % (n - 3); // a in [2, n-2]
        const quint64 g = gcd64(a, n);
        if (g != 1) {
            rep.factor = g;
            rep.method = QString("Fermat round %1 — gcd revealed a factor").arg(i);
            rep.trace << QString("round %1: a = %2, gcd(a, n) = %3 → composite.").arg(i).arg(a).arg(g);
            return;
        }
        if (powmod(a, n - 1, n) != 1) {
            rep.witness = a;
            rep.method = QString("Fermat round %1 — a^(n-1) != 1 (mod n)").arg(i);
            rep.trace << QString("round %1: a = %2 FAILS Fermat's little theorem → certainly composite.").arg(i).arg(a);
            return;
        }
        rep.trace << QString("round %1: a = %2 passed.").arg(i).arg(a);
    }
    rep.prime = true;
    rep.certain = false;
    rep.method = QString("Fermat — %1/%1 rounds passed (PROBABILISTIC)").arg(rounds);
    rep.trace << QStringLiteral("All rounds passed: probably prime, but never a proof — Carmichael numbers (e.g. 561) fool Fermat.");
}

// The hybrid entry point used by both CLI and GUI
static Report checkNumber(quint64 n, Mode mode, int fermatRounds)
{
    Report rep;
    rep.n = n;
    QElapsedTimer timer;
    timer.start();

    if (n < 2) {
        rep.defined = false;
        rep.method = QStringLiteral("definition: n < 2");
        rep.trace << QStringLiteral("The smallest prime is 2; 0 and 1 are not prime by definition.");
        rep.micros = timer.nsecsElapsed() / 1000;
        return rep;
    }

    if (mode == Mode::Fermat) {
        runFermat(rep, fermatRounds);
    } else if (mode == Mode::MillerRabinOnly) {
        rep.trace << QStringLiteral("Stage 1  skipped (Miller-Rabin-only mode: no trial division).");
        runMillerRabin(rep);
    } else {
        quint64 factor = 0;
        qint64 divisions = 0;
        const int t = trialStage(n, factor, divisions);
        if (t == 1) {
            rep.prime = true;
            rep.method = QStringLiteral("trial division — no factor <= sqrt(n)");
            rep.trace << QString("Stage 1  trial division: %1 divisions by primes <= %2, none divide n.")
                             .arg(divisions).arg(TRIAL_LIMIT);
            rep.trace << QStringLiteral("         Every composite has a prime factor <= sqrt(n), so n is certainly prime.");
        } else if (t == -1) {
            rep.factor = factor;
            rep.method = QStringLiteral("trial division — small factor found");
            rep.trace << QString("Stage 1  trial division: %1 divides n (after %2 divisions).")
                             .arg(factor).arg(divisions);
            rep.trace << QString("         n = %1 * %2  →  certainly composite.").arg(factor).arg(n / factor);
        } else if (mode == Mode::TrialOnly) {
            rep.inconclusive = true;
            rep.method = QStringLiteral("trial division — inconclusive past the 10^10 cap");
            rep.trace << QString("Stage 1  trial division: no factor among all %1 primes <= %2.")
                             .arg(smallPrimes().size()).arg(TRIAL_LIMIT);
            rep.trace << QStringLiteral("         Trial-only mode stops here (n > 10^10). Hybrid mode escalates to Miller-Rabin.");
        } else {
            rep.trace << QString("Stage 1  trial division: no factor among all %1 primes <= %2  →  n > 10^10, escalating.")
                             .arg(smallPrimes().size()).arg(TRIAL_LIMIT);
            runMillerRabin(rep);
        }
    }

    rep.micros = timer.nsecsElapsed() / 1000;
    return rep;
}

/* =========================================================================
 *  FORMATTING / PARSING HELPERS (shared by CLI and GUI)
 * ========================================================================= */

static QString verdictWord(const Report &rep)
{
    if (!rep.defined) return QStringLiteral("NOT-PRIME");
    if (rep.inconclusive) return QStringLiteral("INCONCLUSIVE");
    if (rep.prime) return rep.certain ? QStringLiteral("PRIME") : QStringLiteral("PROBABLY-PRIME");
    return QStringLiteral("COMPOSITE");
}

static QString formatMicros(qint64 us)
{
    if (us < 1000) return QString("%1 µs").arg(us);
    if (us < 1000000) return QString("%1 ms").arg(us / 1000.0, 0, 'f', 2);
    return QString("%1 s").arg(us / 1000000.0, 0, 'f', 3);
}

// Accepts digit separators , _ ' and spaces. Max 20 digits (2^64 - 1).
static bool parseNumber(const QString &raw, quint64 *value)
{
    QString digits;
    digits.reserve(raw.size());
    for (int i = 0; i < raw.size(); ++i) {
        const QChar c = raw.at(i);
        if (c.isDigit()) digits += c;
        else if (c == QLatin1Char(',') || c == QLatin1Char('_') || c == QLatin1Char('\'') || c.isSpace()) continue;
        else return false;
    }
    if (digits.isEmpty() || digits.size() > 20) return false;
    bool ok = false;
    const quint64 v = digits.toULongLong(&ok);   // fails cleanly on overflow
    if (ok) *value = v;
    return ok;
}

static QString buildDetailText(const Report &rep)
{
    QString s;
    const auto line = [&s](const QString &label, const QString &value) {
        s += QStringLiteral("%1  %2\n").arg(label, -11).arg(value);
    };
    line(QStringLiteral("n"), QLocale::c().toString((qulonglong)rep.n));
    line(QStringLiteral("raw"), QString::number(rep.n));
    QString verdict = verdictWord(rep);
    if (rep.defined && !rep.inconclusive)
        verdict += rep.prime ? (rep.certain ? QStringLiteral("  (certain)") : QStringLiteral("  (probabilistic)"))
                             : QStringLiteral("  (certain)");
    line(QStringLiteral("verdict"), verdict);
    line(QStringLiteral("method"), rep.method);
    if (rep.factor)
        line(QStringLiteral("factor"), QString("%1  (n = %1 * %2)").arg(rep.factor).arg(rep.n / rep.factor));
    if (rep.witness)
        line(QStringLiteral("witness"), QString("base %1").arg(rep.witness));
    for (const QString &t : rep.trace)
        s += QLatin1String("  ") + t + QLatin1Char('\n');
    line(QStringLiteral("elapsed"), formatMicros(rep.micros));
    return s;
}

/* =========================================================================
 *  CLI
 * ========================================================================= */

struct CliOptions
{
    bool quiet = false;
    bool verbose = false;
    Mode mode = Mode::Auto;
    int fermatRounds = 10;
    bool doList = false;
    quint64 listLimit = 0;
    bool selfTest = false;
    bool readStdin = false;
    QStringList numbers;
};

static QString helpText()
{
    return QStringLiteral(R"(primecheck — hybrid primality tester (Qt 5.12)

USAGE
  primecheck [options] NUMBER [NUMBER...]
  echo "7919 561" | primecheck -

NUMBERS
  Up to 20 digits (max 18446744073709551615). Separators , _ ' and spaces
  are ignored:  1,000,003  ==  1_000_003  ==  1000003.

OPTIONS
  -h, --help         show this help
  -V, --version      version + parameter summary
  -q, --quiet        print only PRIME / COMPOSITE / ... (one line per number)
  -v, --verbose      print the full trace of every stage
  -f, --fermat       use Fermat's little theorem instead of the hybrid core
      --rounds N     Fermat rounds, 1..1000 (default 10)
      --trial        trial division only (exact; inconclusive past 10^10)
      --mr           Miller-Rabin only (skips the trial-division stage)
      --list N       print all primes <= N (N <= 10,000,000)
      --selftest     run the built-in known-answer test suite
      --gui          open the GUI instead (optionally prefill NUMBER)

HOW THE HYBRID CORE WORKS
  Stage 1  Trial division by the 9,592 pre-sieved primes <= 100,000.
           Kills most small composites instantly and is a complete proof
           for every n < 10^10 (any composite has a prime factor <= sqrt(n)).
  Stage 2  Deterministic Miller-Rabin with the first 12 prime bases
           (2 ... 37). This is proven exact for every n < 3.3 * 10^24, so
           across the whole 64-bit range the answer is a proof, not a guess.
  Optional Fermat mode (a^(n-1) = 1 mod n) is kept for education: a failure
           proves compositeness, but a pass is only evidence — Carmichael
           numbers such as 561 pass it for every coprime base.

EXIT CODES
  0 all numbers prime      1 at least one not prime
  2 usage / parse error    3 inconclusive (--trial beyond its cap)

EXAMPLES
  primecheck 2147483647
  primecheck -v 1000000007 18446744073709551557
  primecheck --fermat --rounds 20 561        # Carmichael number fools Fermat
  primecheck --list 1000
  primecheck -q 8911; echo "exit=$?"
)");
}

static void printVersion(QTextStream &out)
{
    out << "primecheck 1.0 — hybrid primality tester\n"
        << "  Qt runtime " << qVersion() << " (built " QT_VERSION_STR ")\n"
        << "  deterministic Miller-Rabin bases: 2 3 5 7 11 13 17 19 23 29 31 37\n"
        << "  trial-division sieve: primes <= " << TRIAL_LIMIT
        << " (" << smallPrimes().size() << " primes)\n";
}

static void printReport(QTextStream &out, const Report &rep, const CliOptions &opt)
{
    if (opt.quiet) { out << verdictWord(rep) << "\n"; return; }

    out << "\n" << QString::number(rep.n) << "  ->  " << verdictWord(rep) << "\n";
    out << "  method   " << rep.method << "\n";
    if (rep.factor)
        out << "  factor   " << rep.factor << "   (n = " << rep.factor
            << " * " << (rep.n / rep.factor) << ")\n";
    if (rep.witness)
        out << "  witness  base " << rep.witness << " proves compositeness\n";
    if (opt.verbose)
        for (const QString &line : rep.trace) out << "  " << line << "\n";
    out << "  elapsed  " << formatMicros(rep.micros) << "\n";
}

static int runList(QTextStream &out, QTextStream &err, quint64 limit)
{
    const quint64 cap = 10000000;
    if (limit > cap) { err << "error: --list limit capped at " << cap << "\n"; return 2; }
    QElapsedTimer t; t.start();
    const std::vector<quint64> primes = primesUpTo(limit);
    int col = 0;
    for (size_t i = 0; i < primes.size(); ++i) {
        out << qSetFieldWidth(12) << right << QString::number(primes[i]) << qSetFieldWidth(0);
        if (++col == 6) { out << "\n"; col = 0; }
    }
    if (col) out << "\n";
    out << primes.size() << " primes <= " << limit
        << "  (" << formatMicros(t.nsecsElapsed() / 1000) << ")\n";
    return 0;
}

static int runSelfTest(QTextStream &out)
{
    struct Case { quint64 n; bool prime; const char *note; };
    static const Case cases[] = {
        { 0,                      false, "definition" },
        { 1,                      false, "definition" },
        { 2,                      true,  "smallest prime" },
        { 4,                      false, "even" },
        { 561,                    false, "Carmichael number" },
        { 8911,                   false, "Carmichael number" },
        { 7919,                   true,  "the 1000th prime" },
        { 2147483647,             true,  "Mersenne prime 2^31 - 1" },
        { 3215031751ULL,          false, "strong pseudoprime to bases 2,3,5,7" },
        { 1000000007,             true,  "the famous 10^9 + 7" },
        { 999999999989ULL,        true,  "largest prime < 10^12" },
        { 1000000000039ULL,       true,  "smallest prime > 10^12 (Miller-Rabin path)" },
        { 1000000016000000063ULL, false, "(10^9+7)(10^9+9) — Miller-Rabin path" },
        { 2305843009213693951ULL, true,  "Mersenne prime 2^61 - 1" },
        { 18446744073709551557ULL,true,  "largest 64-bit prime" },
        { 18446744073709551615ULL,false, "2^64 - 1" },
    };
    out << "self-test (auto/hybrid mode):\n";
    int failed = 0;
    for (const Case &c : cases) {
        const Report rep = checkNumber(c.n, Mode::Auto, 1);
        const bool got = rep.defined && rep.prime && !rep.inconclusive;
        const bool ok = (got == c.prime);
        if (!ok) ++failed;
        out << "  " << (ok ? "ok    " : "FAIL  ")
            << left << qSetFieldWidth(21) << QString::number(c.n) << qSetFieldWidth(0)
            << right << (c.prime ? "prime     " : "composite ") << c.note << "\n";
    }
    out << (failed ? QString("%1 case(s) FAILED\n").arg(failed)
                   : QStringLiteral("all cases passed\n"));
    return failed ? 1 : 0;
}

static int runCli(const QStringList &args)
{
    QTextStream out(stdout);
    QTextStream err(stderr);
    int code = 0;

    CliOptions opt;
    for (int i = 0; i < args.size(); ++i) {
        const QString &a = args.at(i);
        if (a == QLatin1String("-h") || a == QLatin1String("--help")) { out << helpText(); out.flush(); return 0; }
        if (a == QLatin1String("-V") || a == QLatin1String("--version")) { printVersion(out); out.flush(); return 0; }
        if (a == QLatin1String("-q") || a == QLatin1String("--quiet")) { opt.quiet = true; continue; }
        if (a == QLatin1String("-v") || a == QLatin1String("--verbose")) { opt.verbose = true; continue; }
        if (a == QLatin1String("--trial")) { opt.mode = Mode::TrialOnly; continue; }
        if (a == QLatin1String("--mr")) { opt.mode = Mode::MillerRabinOnly; continue; }
        if (a == QLatin1String("-f") || a == QLatin1String("--fermat")) { opt.mode = Mode::Fermat; continue; }
        if (a == QLatin1String("--rounds")) {
            if (i + 1 >= args.size()) { err << "error: --rounds needs a number\n"; err.flush(); return 2; }
            bool ok; const int r = args.at(++i).toInt(&ok);
            if (!ok || r < 1 || r > 1000) { err << "error: --rounds must be 1..1000\n"; err.flush(); return 2; }
            opt.fermatRounds = r;
            opt.mode = Mode::Fermat;
            continue;
        }
        if (a == QLatin1String("--list")) {
            if (i + 1 >= args.size()) { err << "error: --list needs a limit\n"; err.flush(); return 2; }
            bool ok; const quint64 lim = args.at(++i).toULongLong(&ok);
            if (!ok || lim < 2) { err << "error: bad --list limit\n"; err.flush(); return 2; }
            opt.doList = true;
            opt.listLimit = lim;
            continue;
        }
        if (a == QLatin1String("--selftest")) { opt.selfTest = true; continue; }
        if (a == QLatin1String("-")) { opt.readStdin = true; continue; }
        if (a.startsWith(QLatin1Char('-'))) {
            bool hasDigit = false;
            for (int k = 0; k < a.size(); ++k)
                if (a.at(k).isDigit()) { hasDigit = true; break; }
            if (!hasDigit) {
                err << "error: unknown option '" << a << "' — try --help\n";
                err.flush();
                return 2;
            }
        }
        opt.numbers << a;
    }

    if (opt.selfTest) { code = runSelfTest(out); out.flush(); return code; }
    if (opt.doList)   { code = runList(out, err, opt.listLimit); out.flush(); err.flush(); return code; }

    if (opt.readStdin) {
        QTextStream in(stdin);
        while (!in.atEnd()) {
            const QStringList tokens =
                in.readLine().simplified().split(QLatin1Char(' '), QString::SkipEmptyParts);
            for (const QString &t : tokens) opt.numbers << t;
        }
    }

    if (opt.numbers.isEmpty()) { out << helpText(); out.flush(); return 2; }

    int primes = 0, notPrime = 0, inconclusive = 0, invalid = 0;
    for (const QString &token : opt.numbers) {
        quint64 n = 0;
        if (!parseNumber(token, &n)) {
            err << "error: '" << token << "' is not a valid number (max 18446744073709551615)\n";
            ++invalid;
            continue;
        }
        const Report rep = checkNumber(n, opt.mode, opt.fermatRounds);
        printReport(out, rep, opt);
        if (!rep.defined)          ++notPrime;
        else if (rep.inconclusive) ++inconclusive;
        else if (rep.prime)        ++primes;
        else                       ++notPrime;
    }

    if (opt.numbers.size() > 1 && !opt.quiet)
        out << "\nsummary  " << primes << " prime, " << notPrime << " not prime, "
            << inconclusive << " inconclusive\n";

    if (invalid)      code = 2;
    else if (notPrime) code = 1;
    else if (inconclusive) code = 3;

    out.flush();
    err.flush();
    return code;
}

/* =========================================================================
 *  GUI  (no Q_OBJECT on purpose: the file needs no moc pass at all)
 * ========================================================================= */

class CheckerWindow : public QWidget
{
public:
    explicit CheckerWindow(const QString &prefill, QWidget *parent = nullptr)
        : QWidget(parent)
    {
        setWindowTitle(QStringLiteral("Prime Checker — hybrid (Qt %1)").arg(QT_VERSION_STR));
        resize(640, 680);

        QFont mono(QStringLiteral("Monospace"));
        mono.setStyleHint(QFont::TypeWriter);

        QLabel *title = new QLabel(QStringLiteral("Prime Checker"), this);
        QFont tf = title->font();
        tf.setPointSize(tf.pointSize() + 6);
        tf.setBold(true);
        title->setFont(tf);

        QLabel *subtitle = new QLabel(
            QStringLiteral("Trial division → deterministic Miller-Rabin (exact for all 64-bit n), "
                           "with optional Fermat mode"), this);
        subtitle->setWordWrap(true);
        subtitle->setStyleSheet(QStringLiteral("color:#666;"));

        m_input = new QLineEdit(this);
        m_input->setFont(mono);
        m_input->setPlaceholderText(QStringLiteral("number <= 18,446,744,073,709,551,615 — separators , _ ' ok"));
        if (!prefill.isEmpty()) m_input->setText(prefill);

        QPushButton *btnRandom = new QPushButton(QStringLiteral("Random"), this);
        QPushButton *btnCheck  = new QPushButton(QStringLiteral("Check  ✓"), this);

        m_algo = new QComboBox(this);
        m_algo->addItem(QStringLiteral("Hybrid (auto) — recommended"));
        m_algo->addItem(QStringLiteral("Trial division only — exact, capped at 10^10"));
        m_algo->addItem(QStringLiteral("Miller-Rabin only — deterministic, 12 bases"));
        m_algo->addItem(QStringLiteral("Fermat only — probabilistic (educational)"));

        QLabel *roundsLabel = new QLabel(QStringLiteral("Fermat rounds:"), this);
        m_rounds = new QSpinBox(this);
        m_rounds->setRange(1, 100);
        m_rounds->setValue(10);
        m_rounds->setEnabled(false);

        m_verdict = new QLabel(this);
        m_verdict->setAlignment(Qt::AlignCenter);
        m_verdict->setMinimumHeight(64);
        applyVerdict(QStringLiteral("Enter a number and press Check."), 0);

        m_detail = new QLabel(this);
        m_detail->setFont(mono);
        m_detail->setTextFormat(Qt::PlainText);
        m_detail->setTextInteractionFlags(Qt::TextSelectableByMouse);
        m_detail->setWordWrap(true);
        m_detail->setMinimumHeight(180);
        m_detail->setAlignment(Qt::AlignTop | Qt::AlignLeft);
        m_detail->setStyleSheet(QStringLiteral(
            "background:#f7f6f3; border:1px solid #ddd; border-radius:6px; padding:10px;"));

        m_history = new QListWidget(this);
        m_history->setFont(mono);
        QGroupBox *historyBox = new QGroupBox(QStringLiteral("History"), this);
        QVBoxLayout *hLay = new QVBoxLayout(historyBox);
        hLay->addWidget(m_history);

        QHBoxLayout *inputRow = new QHBoxLayout();
        inputRow->addWidget(m_input, 1);
        inputRow->addWidget(btnRandom);
        inputRow->addWidget(btnCheck);

        QHBoxLayout *optRow = new QHBoxLayout();
        optRow->addWidget(m_algo, 1);
        optRow->addWidget(roundsLabel);
        optRow->addWidget(m_rounds);

        QVBoxLayout *lay = new QVBoxLayout(this);
        lay->addWidget(title);
        lay->addWidget(subtitle);
        lay->addSpacing(6);
        lay->addLayout(inputRow);
        lay->addLayout(optRow);
        lay->addWidget(m_verdict);
        lay->addWidget(m_detail);
        lay->addWidget(historyBox, 1);

        connect(btnCheck, &QPushButton::clicked, this, [this] { runCheck(); });
        connect(m_input, &QLineEdit::returnPressed, this, [this] { runCheck(); });
        connect(btnRandom, &QPushButton::clicked, this, [this] {
            quint64 v = QRandomGenerator::global()->generate64() >> 1; // 63-bit
            v |= 1;                                                    // odd
            if (v < 3) v = 3;
            m_input->setText(QString::number(v));
            runCheck();
        });
        connect(m_algo, QOverload<int>::of(&QComboBox::currentIndexChanged), this,
                [this](int index) { m_rounds->setEnabled(index == (int)Mode::Fermat); });

        m_input->setFocus();
    }

    void runCheck()
    {
        quint64 n = 0;
        if (!parseNumber(m_input->text(), &n)) {
            applyVerdict(QStringLiteral("Invalid input"), 3);
            m_detail->setText(QStringLiteral(
                "Could not parse the input.\n"
                "Allowed: up to 20 digits, maximum 18,446,744,073,709,551,615.\n"
                "Separators , _ ' and spaces are ignored."));
            return;
        }

        const Report rep = checkNumber(n, static_cast<Mode>(m_algo->currentIndex()), m_rounds->value());
        const QString word = verdictWord(rep);

        int kind = 0; // 0 neutral, 1 prime, 2 composite, 3 amber
        if (!rep.defined || rep.inconclusive) kind = 3;
        else if (rep.prime) kind = 1;
        else kind = 2;
        applyVerdict(word, kind);

        m_detail->setText(buildDetailText(rep));

        m_history->insertItem(0, QString("%1   %2   %3   %4")
            .arg(QTime::currentTime().toString(QStringLiteral("HH:mm:ss")))
            .arg(QString::number(rep.n))
            .arg(word)
            .arg(formatMicros(rep.micros)));
        while (m_history->count() > 200)
            delete m_history->takeItem(m_history->count() - 1);
    }

private:
    void applyVerdict(const QString &text, int kind)
    {
        static const char *colors[][2] = {
            { "#555555", "#eeeeee" },   // neutral
            { "#157f3d", "#e8f5e9" },   // prime
            { "#c0392b", "#fdecea" },   // composite
            { "#b07d00", "#fff8e1" },   // not-prime / inconclusive / invalid
        };
        m_verdict->setText(text);
        m_verdict->setStyleSheet(QStringLiteral(
            "font-size:24px; font-weight:bold; color:%1; background:%2;"
            "border:1px solid %1; border-radius:6px; padding:12px;")
            .arg(QLatin1String(colors[kind][0]), QLatin1String(colors[kind][1])));
    }

    QLineEdit   *m_input = nullptr;
    QComboBox   *m_algo = nullptr;
    QSpinBox    *m_rounds = nullptr;
    QLabel      *m_verdict = nullptr;
    QLabel      *m_detail = nullptr;
    QListWidget *m_history = nullptr;
};

/* =========================================================================
 *  DISPATCH — no args (or --gui) → GUI, anything else → CLI
 * ========================================================================= */

int main(int argc, char *argv[])
{
    QStringList args;
    args.reserve(qMax(0, argc - 1));
    for (int i = 1; i < argc; ++i)
        args << QString::fromLocal8Bit(argv[i]);

    const bool wantGui = args.isEmpty() || args.contains(QLatin1String("--gui"));

    if (wantGui) {
        // QApplication only when we really need widgets — CLI works headless.
        QApplication app(argc, argv);
        app.setApplicationName(QStringLiteral("primecheck"));
        app.setApplicationVersion(QStringLiteral("1.0"));
        QString prefill;
        for (int i = 0; i < args.size(); ++i) {
            if (args.at(i) != QLatin1String("--gui") && !args.at(i).startsWith(QLatin1Char('-'))) {
                prefill = args.at(i);
                break;
            }
        }
        CheckerWindow w(prefill);
        w.show();
        if (!prefill.isEmpty())
            w.runCheck();
        return app.exec();
    }

    QCoreApplication app(argc, argv);
    app.setApplicationName(QStringLiteral("primecheck"));
    app.setApplicationVersion(QStringLiteral("1.0"));
    return runCli(args);
}
