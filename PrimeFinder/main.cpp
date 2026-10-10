/* =========================================================================
 * primefinder.cpp — single-file Qt 5.12 nearest-prime finder (GUI + CLI)
 *
 * Searches outward from N in alternating bands ("batch up, batch down"),
 * so it never marches thousands in one direction before checking the other.
 *
 * Build with qmake — primefinder.pro:
 *     QT       += widgets
 *     CONFIG   += c++11
 *     TARGET    = primefinder
 *     SOURCES  += primefinder.cpp
 *   then:  qmake && make
 *
 * Or manually on Linux:
 *     g++ -fPIC -std=c++11 primefinder.cpp -o primefinder \
 *         $(pkg-config --cflags --libs Qt5Widgets)
 *
 * Usage:
 *     ./primefinder                     → GUI
 *     ./primefinder 1000000000          → CLI, alternating bands of 50
 *     ./primefinder --dir full 1000000000
 *     ./primefinder --gui 99
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
#include <QVBoxLayout>
#include <QWidget>

#include <limits>
#include <vector>

static const quint64 MAX64 = std::numeric_limits<quint64>::max();

/* =========================================================================
 *  PRIME CORE — trial division (primes <= 100000), then deterministic
 *  Miller-Rabin with bases 2..37 (exact for every 64-bit n)
 * ========================================================================= */

static const quint64 TRIAL_LIMIT = 100000;

static inline quint64 addmod(quint64 a, quint64 b, quint64 m)
{
    return (a >= m - b) ? (a - (m - b)) : (a + b);
}

static inline quint64 mulmod(quint64 a, quint64 b, quint64 m)
{
#if defined(__SIZEOF_INT128__)
    return (quint64)(((unsigned __int128)(a % m) * (b % m)) % m);
#else
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

// returns 1 = proved prime, -1 = composite (factor set), 0 = inconclusive
static int trialStage(quint64 n, quint64 &factor)
{
    const std::vector<quint64> &primes = smallPrimes();
    for (size_t i = 0; i < primes.size(); ++i) {
        const quint64 p = primes[i];
        if (p > n / p) return 1;
        if (n % p == 0) { factor = p; return -1; }
    }
    return 0;
}

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

// Deterministic for every 64-bit n.
static bool isPrimeExact(quint64 n)
{
    if (n < 2) return false;
    quint64 factor = 0;
    const int t = trialStage(n, factor);
    if (t == 1) return true;
    if (t == -1) return false;

    quint64 d = n - 1;
    int s = 0;
    while ((d & 1) == 0) { d >>= 1; ++s; }
    static const quint64 bases[] = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37 };
    for (size_t i = 0; i < sizeof(bases) / sizeof(bases[0]); ++i) {
        const quint64 a = bases[i];
        if (a % n == 0) continue;
        if (!mrPass(a, n, d, s)) return false;
    }
    return true;
}

/* =========================================================================
 *  FINDER — alternating band search
 * ========================================================================= */

enum class Direction { Both = 0, Up = 1, Down = 2, Full = 3 };

struct FinderParams
{
    quint64 start = 0;
    int batch = 50;                  // window size per direction per round
    Direction dir = Direction::Both;
    quint64 limit = 1000000;         // max distance per direction
    bool verbose = false;            // trace every tested candidate
};

struct FinderReport
{
    quint64 start = 0;
    bool startIsPrime = false;
    bool foundUp = false, foundDown = false;
    quint64 upPrime = 0, downPrime = 0;
    quint64 upDist = 0, downDist = 0;
    bool equidistant = false;
    bool hitLimit = false;
    bool downCutOff = false;         // down search stopped early after an up win
    quint64 candidates = 0;          // actual primality tests performed
    quint64 bands = 0;
    QStringList trace;
    qint64 micros = 0;
};

// Scan one band nearest-first. Returns 0 = no prime, 1 = found, 2 = cut off.
static int scanBand(bool up, quint64 start, quint64 dLo, quint64 dHi, quint64 stopDist,
                    quint64 &tested, quint64 &foundValue, quint64 &foundDist,
                    QStringList &trace, bool verbose)
{
    const QString dirTxt = up ? QStringLiteral("up  ") : QStringLiteral("down");
    quint64 local = 0;
    for (quint64 d = dLo; d <= dHi; ++d) {
        if (d >= stopDist) {
            trace << QString("%1 d %2..%3  →  stopped early (%4 candidate(s)); cannot beat %5%6")
                         .arg(dirTxt).arg(dLo).arg(dHi).arg(local)
                         .arg(up ? QStringLiteral("+") : QStringLiteral("-")).arg(stopDist);
            return 2;
        }
        const quint64 value = up ? start + d : start - d;
        if ((value & 1) == 0 && value != 2) continue;   // evens never prime (2 handled)
        ++tested;
        ++local;
        if (isPrimeExact(value)) {
            foundValue = value;
            foundDist = d;
            if (verbose)
                trace << QString("      %1  →  PRIME").arg(value);
            trace << QString("%1 d %2..%3  →  PRIME %4 (%5%6) after %7 candidate(s)")
                         .arg(dirTxt).arg(dLo).arg(dHi).arg(value)
                         .arg(up ? QStringLiteral("+") : QStringLiteral("-")).arg(d).arg(local);
            return 1;
        }
        if (verbose)
            trace << QString("      %1  →  composite").arg(value);
    }
    trace << QString("%1 d %2..%3  →  no prime (%4 candidate(s))")
                 .arg(dirTxt).arg(dLo).arg(dHi).arg(local);
    return 0;
}

enum class SearchEnd { Found, Limit, Exhausted };

// One-directional search in bands until a prime, the limit, or the boundary.
static SearchEnd searchDirection(bool up, const FinderParams &p, FinderReport &r)
{
    quint64 dLo = 1;
    while (dLo <= p.limit) {
        quint64 dHi = qMin<quint64>(dLo + p.batch - 1, p.limit);
        if (up) {
            if (p.start >= MAX64) {
                r.trace << QStringLiteral("up    64-bit ceiling — no candidates above start");
                return SearchEnd::Exhausted;
            }
            dHi = qMin(dHi, MAX64 - p.start);
        } else {
            if (p.start <= 2) {
                r.trace << QStringLiteral("down  floor — no prime exists below 2");
                return SearchEnd::Exhausted;
            }
            dHi = qMin(dHi, p.start - 2);   // candidate value must stay >= 2
        }
        ++r.bands;
        if (dHi < dLo) {
            r.trace << (up ? QStringLiteral("up    band empty at boundary")
                           : QStringLiteral("down  band empty at boundary"));
            return SearchEnd::Exhausted;
        }
        quint64 value = 0, dist = 0;
        const int st = scanBand(up, p.start, dLo, dHi, MAX64, r.candidates,
                                value, dist, r.trace, p.verbose);
        if (st == 1) {
            if (up) { r.foundUp = true; r.upPrime = value; r.upDist = dist; }
            else    { r.foundDown = true; r.downPrime = value; r.downDist = dist; }
            return SearchEnd::Found;
        }
        dLo = dHi + 1;
    }
    return SearchEnd::Limit;
}

// Alternating: up band, down band, up band, ... stops at the first round
// that yields a prime — which is guaranteed to contain the global nearest.
static FinderReport runAlternating(const FinderParams &p)
{
    FinderReport r;
    r.start = p.start;
    QElapsedTimer t;
    t.start();

    ++r.candidates;
    if (isPrimeExact(p.start)) {
        r.startIsPrime = true;
        r.trace << QStringLiteral("start value is itself prime — nothing to search.");
        r.micros = t.nsecsElapsed() / 1000;
        return r;
    }
    r.trace << QString("start %1 composite — alternating bands of %2 (odd candidates only).")
                   .arg(p.start).arg(p.batch);

    quint64 dLo = 1;
    bool done = false;
    while (dLo <= p.limit && !done) {
        const quint64 dHiBase = qMin<quint64>(dLo + p.batch - 1, p.limit);
        ++r.bands;

        bool gotUp = false;
        quint64 upV = 0, upD = 0;
        if (p.start >= MAX64) {
            r.trace << QStringLiteral("up    64-bit ceiling — no candidates");
        } else {
            const quint64 upHi = qMin(dHiBase, MAX64 - p.start);
            if (upHi < dLo) {
                r.trace << QStringLiteral("up    band empty at boundary");
            } else {
                gotUp = (scanBand(true, p.start, dLo, upHi, MAX64, r.candidates,
                                  upV, upD, r.trace, p.verbose) == 1);
            }
        }

        const quint64 stopDist = gotUp ? upD : MAX64;   // down can only win if closer

        bool gotDown = false;
        quint64 dnV = 0, dnD = 0;
        if (p.start <= 2) {
            r.trace << QStringLiteral("down  floor at 2 — no candidates");
        } else {
            const quint64 dnHi = qMin(dHiBase, p.start - 2);
            if (dnHi < dLo) {
                r.trace << QStringLiteral("down  band empty at boundary");
            } else {
                const int st = scanBand(false, p.start, dLo, dnHi, stopDist, r.candidates,
                                        dnV, dnD, r.trace, p.verbose);
                gotDown = (st == 1);
                r.downCutOff = (st == 2);
            }
        }

        if (gotUp || gotDown) {
            r.foundUp = gotUp;   r.upPrime = upV;   r.upDist = upD;
            r.foundDown = gotDown; r.downPrime = dnV; r.downDist = dnD;
            r.equidistant = gotUp && gotDown && upD == dnD;
            done = true;
        } else {
            dLo = dHiBase + 1;
        }
    }
    r.hitLimit = !done;
    if (r.hitLimit)
        r.trace << QString("distance limit %1 reached without finding a prime.").arg(p.limit);
    r.micros = t.nsecsElapsed() / 1000;
    return r;
}

static FinderReport runDirectional(const FinderParams &p, bool up)
{
    FinderReport r;
    r.start = p.start;
    QElapsedTimer t;
    t.start();
    r.trace << QString("searching %1 from %2 in bands of %3 (start value itself excluded).")
                   .arg(up ? QStringLiteral("up") : QStringLiteral("down"))
                   .arg(p.start).arg(p.batch);
    const SearchEnd end = searchDirection(up, p, r);
    r.hitLimit = (end == SearchEnd::Limit);
    r.micros = t.nsecsElapsed() / 1000;
    return r;
}

// Independent full searches in both directions (reports nearest up AND down).
static FinderReport runFull(const FinderParams &p)
{
    FinderReport r;
    r.start = p.start;
    QElapsedTimer t;
    t.start();
    ++r.candidates;
    if (isPrimeExact(p.start)) {
        r.startIsPrime = true;
        r.trace << QStringLiteral("start value is itself prime — nothing to search.");
        r.micros = t.nsecsElapsed() / 1000;
        return r;
    }
    r.trace << QString("start %1 composite — independent up and down searches, bands of %2.")
                   .arg(p.start).arg(p.batch);
    const SearchEnd endUp = searchDirection(true, p, r);
    const SearchEnd endDn = searchDirection(false, p, r);
    if (r.foundUp && r.foundDown && r.upDist == r.downDist)
        r.equidistant = true;
    r.hitLimit = (endUp == SearchEnd::Limit || endDn == SearchEnd::Limit)
                 && !r.foundUp && !r.foundDown;
    r.micros = t.nsecsElapsed() / 1000;
    return r;
}

static FinderReport findNearest(const FinderParams &p)
{
    switch (p.dir) {
    case Direction::Up:   return runDirectional(p, true);
    case Direction::Down: return runDirectional(p, false);
    case Direction::Full: return runFull(p);
    case Direction::Both:
    default:              return runAlternating(p);
    }
}

/* =========================================================================
 *  SHARED HELPERS
 * ========================================================================= */

static QString formatMicros(qint64 us)
{
    if (us < 1000) return QString("%1 µs").arg(us);
    if (us < 1000000) return QString("%1 ms").arg(us / 1000.0, 0, 'f', 2);
    return QString("%1 s").arg(us / 1000000.0, 0, 'f', 3);
}

static QString grouped(quint64 v)
{
    return QLocale::c().toString((qulonglong)v);
}

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
    const quint64 v = digits.toULongLong(&ok);
    if (ok) *value = v;
    return ok;
}

static QString strategyText(const FinderParams &p)
{
    QString s;
    switch (p.dir) {
    case Direction::Both: s = QString("alternating bands of %1 (up band, down band, …)").arg(p.batch); break;
    case Direction::Up:   s = QString("up only, bands of %1 (start excluded)").arg(p.batch); break;
    case Direction::Down: s = QString("down only, bands of %1 (start excluded)").arg(p.batch); break;
    case Direction::Full: s = QString("independent up + down searches, bands of %1").arg(p.batch); break;
    }
    return s + QString(", distance limit %1").arg(p.limit);
}

static QString notFoundReason(const FinderReport &r, bool up, const FinderParams &p)
{
    if (up && r.start >= MAX64) return QStringLiteral("no larger number exists (64-bit ceiling)");
    if (!up && r.start <= 2)    return QStringLiteral("no prime exists below 2");
    return QString("no prime within distance %1").arg(p.limit);
}

static QString finderDetailText(const FinderReport &r, const FinderParams &p)
{
    QString s;
    const auto line = [&s](const QString &label, const QString &value) {
        s += QStringLiteral("%1  %2\n").arg(label, -13).arg(value);
    };
    line(QStringLiteral("start"), grouped(r.start));
    line(QStringLiteral("strategy"), strategyText(p));
    if (r.startIsPrime) {
        line(QStringLiteral("verdict"), QStringLiteral("start value is itself prime"));
    } else {
        const bool upRelevant = p.dir != Direction::Down;
        const bool dnRelevant = p.dir != Direction::Up;
        if (upRelevant) {
            line(QStringLiteral("nearest up"),
                 r.foundUp ? QString("%1  (distance %2)").arg(grouped(r.upPrime)).arg(r.upDist)
                           : notFoundReason(r, true, p));
        }
        if (dnRelevant) {
            QString dn;
            if (r.foundDown) dn = QString("%1  (distance %2)").arg(grouped(r.downPrime)).arg(r.downDist);
            else if (r.downCutOff && r.foundUp) dn = QString("not determined — search cut off (up won at +%1)").arg(r.upDist);
            else dn = notFoundReason(r, false, p);
            line(QStringLiteral("nearest down"), dn);
        }
        if (r.foundUp || r.foundDown) {
            if (r.equidistant)
                line(QStringLiteral("answer"), QString("TWO equidistant primes: %1 (down) and %2 (up), distance %3")
                        .arg(grouped(r.downPrime)).arg(grouped(r.upPrime)).arg(r.upDist));
            else if (r.foundUp && (!r.foundDown || r.upDist <= r.downDist))
                line(QStringLiteral("answer"), QString("%1  — distance %2, up").arg(grouped(r.upPrime)).arg(r.upDist));
            else
                line(QStringLiteral("answer"), QString("%1  — distance %2, down").arg(grouped(r.downPrime)).arg(r.downDist));
        }
    }
    line(QStringLiteral("candidates"), QString("%1 primality tests (even numbers skipped)").arg(r.candidates));
    line(QStringLiteral("bands"), QString("%1 band(s)").arg(r.bands));
    line(QStringLiteral("elapsed"), formatMicros(r.micros));
    return s;
}

/* =========================================================================
 *  CLI
 * ========================================================================= */

struct CliOptions
{
    bool quiet = false;
    bool verbose = false;
    bool selfTest = false;
    Direction dir = Direction::Both;
    int batch = 50;
    quint64 limit = 1000000;
    QStringList positionals;
};

static QString helpText()
{
    return QStringLiteral(R"(primefinder — batched bidirectional nearest-prime search (Qt 5.12)

USAGE
  primefinder [options] START

OPTIONS
  -h, --help          show this help
  -V, --version       version info
  -b, --batch N       band size per direction per round, 1..100000 (default 50)
      --dir MODE      both (default) | up | down | full
                        both : alternating bands, stops at the nearest prime
                        up   : next prime only (start value excluded)
                        down : previous prime only (start value excluded)
                        full : report nearest up AND nearest down independently
      --limit D       max search distance per direction, default 1000000
  -q, --quiet         print only the answer value (NONE if not found)
  -v, --verbose       trace every tested candidate
      --selftest      run built-in known-answer tests
      --gui           launch the GUI instead (optionally prefill START)

HOW IT WORKS
  Instead of marching thousands of candidates in one direction before trying
  the other, the search expands in alternating bands of `batch` values:
    +1..+50 up,  -1..-50 down,  +51..+100 up,  -51..-100 down, ...
  Each band is scanned nearest-first, even candidates are skipped (except 2),
  and once one direction finds a prime the opposite band is cut off the
  moment its distance can no longer win. Bands grow monotonically outward,
  so the first round producing a prime always contains the true nearest
  prime — the batch size affects granularity only, never correctness.
  Primality core: trial division (primes <= 100000), then deterministic
  Miller-Rabin (bases 2..37) — exact for every 64-bit number.

EXIT CODES
  0 found (or start itself prime)    1 nothing within --limit    2 error

EXAMPLES
  primefinder 1000000000
  primefinder -b 20 --dir full 1000000000
  primefinder --dir up 18446744073709551550
  primefinder -q 99
)");
}

static void printFinderReport(QTextStream &out, const FinderReport &r, const FinderParams &p, bool quiet)
{
    const bool found = r.foundUp || r.foundDown;

    if (quiet) {
        if (r.startIsPrime) out << r.start << "\n";
        else if (!found)    out << "NONE\n";
        else if (r.equidistant) out << r.downPrime << "\n" << r.upPrime << "\n";
        else if (r.foundUp && (!r.foundDown || r.upDist <= r.downDist)) out << r.upPrime << "\n";
        else out << r.downPrime << "\n";
        return;
    }

    out << "\nstart      " << r.start << "\n";
    out << "strategy   " << strategyText(p) << "\n\n";
    for (const QString &line : r.trace)
        out << "  " << line << "\n";
    out << "\n";

    if (r.startIsPrime) {
        out << "answer     start value is itself prime\n";
    } else if (!found) {
        out << "answer     no prime found within distance " << p.limit << "\n";
    } else {
        if (r.foundUp)   out << "nearest up    " << r.upPrime << "  (distance " << r.upDist << ")\n";
        if (r.foundDown) out << "nearest down  " << r.downPrime << "  (distance " << r.downDist << ")\n";
        if (r.equidistant) {
            out << "answer     TWO equidistant primes: " << r.downPrime << " (down) and "
                << r.upPrime << " (up), distance " << r.upDist << "\n";
        } else if (r.foundUp && (!r.foundDown || r.upDist <= r.downDist)) {
            out << "answer     " << r.upPrime << "  — distance " << r.upDist << ", direction up\n";
        } else {
            out << "answer     " << r.downPrime << "  — distance " << r.downDist << ", direction down\n";
        }
    }
    out << "stats      " << r.candidates << " candidates, " << r.bands
        << " band(s), " << formatMicros(r.micros) << "\n";
}

static int runSelfTest(QTextStream &out)
{
    int failed = 0;
    const auto check = [&out, &failed](bool ok, const QString &what) {
        out << "  " << (ok ? "ok    " : "FAIL  ") << what << "\n";
        if (!ok) ++failed;
    };

    FinderParams p;
    p.batch = 50;
    p.limit = 1000000;

    // alternating nearest
    p.start = 1000000000;
    FinderReport r = findNearest(p);
    check(r.foundUp && r.upPrime == 1000000007ULL && r.upDist == 7,
          QStringLiteral("nearest to 1000000000 is 1000000007 (+7)"));

    p.start = 99;
    r = findNearest(p);
    check(r.equidistant && r.upPrime == 101 && r.downPrime == 97,
          QStringLiteral("99 is equidistant between 97 and 101 (±2)"));

    p.start = 89;
    r = findNearest(p);
    check(r.startIsPrime, QStringLiteral("89 reports 'start is prime'"));

    // directional (start excluded)
    p.start = 90;
    p.dir = Direction::Up;
    r = findNearest(p);
    check(r.foundUp && r.upPrime == 97, QStringLiteral("next prime after 90 is 97"));
    p.dir = Direction::Down;
    r = findNearest(p);
    check(r.foundDown && r.downPrime == 89, QStringLiteral("previous prime before 90 is 89"));

    p.start = 3;
    p.dir = Direction::Up;
    r = findNearest(p);
    check(r.foundUp && r.upPrime == 5, QStringLiteral("next prime after 3 is 5 (start excluded)"));
    p.dir = Direction::Down;
    r = findNearest(p);
    check(r.foundDown && r.downPrime == 2, QStringLiteral("previous prime before 3 is 2"));

    p.start = 1;
    p.dir = Direction::Up;
    r = findNearest(p);
    check(r.foundUp && r.upPrime == 2, QStringLiteral("next prime after 1 is 2"));
    p.dir = Direction::Down;
    r = findNearest(p);
    check(!r.foundDown, QStringLiteral("no prime below 2"));

    p.start = MAX64;
    p.dir = Direction::Up;
    r = findNearest(p);
    check(!r.foundUp, QStringLiteral("no prime above 2^64 - 1 (ceiling handled)"));
    p.dir = Direction::Down;
    r = findNearest(p);
    check(r.foundDown && r.downPrime == 18446744073709551557ULL && r.downDist == 58,
          QStringLiteral("largest 64-bit prime is 2^64 - 59 (distance 58 from top)"));

    // full mode
    p.start = 1000000000;
    p.dir = Direction::Full;
    r = findNearest(p);
    check(r.foundUp && r.foundDown && r.upPrime == 1000000007ULL && r.downPrime == 999999937ULL,
          QStringLiteral("full mode: 1000000007 up / 999999937 down"));

    out << (failed ? QString("%1 case(s) FAILED\n").arg(failed)
                   : QStringLiteral("all cases passed\n"));
    return failed ? 1 : 0;
}

static int runCli(const QStringList &args)
{
    QTextStream out(stdout);
    QTextStream err(stderr);

    CliOptions opt;
    for (int i = 0; i < args.size(); ++i) {
        const QString &a = args.at(i);
        if (a == QLatin1String("-h") || a == QLatin1String("--help")) { out << helpText(); out.flush(); return 0; }
        if (a == QLatin1String("-V") || a == QLatin1String("--version")) {
            out << "primefinder 1.0 — batched bidirectional nearest-prime search\n"
                << "  Qt runtime " << qVersion() << " (built " QT_VERSION_STR ")\n";
            out.flush();
            return 0;
        }
        if (a == QLatin1String("-q") || a == QLatin1String("--quiet")) { opt.quiet = true; continue; }
        if (a == QLatin1String("-v") || a == QLatin1String("--verbose")) { opt.verbose = true; continue; }
        if (a == QLatin1String("--selftest")) { opt.selfTest = true; continue; }
        if (a == QLatin1String("-b") || a == QLatin1String("--batch")) {
            if (i + 1 >= args.size()) { err << "error: --batch needs a value\n"; err.flush(); return 2; }
            bool ok; const int b = args.at(++i).toInt(&ok);
            if (!ok || b < 1 || b > 100000) { err << "error: --batch must be 1..100000\n"; err.flush(); return 2; }
            opt.batch = b;
            continue;
        }
        if (a == QLatin1String("--dir")) {
            if (i + 1 >= args.size()) { err << "error: --dir needs both|up|down|full\n"; err.flush(); return 2; }
            const QString m = args.at(++i).toLower();
            if (m == QLatin1String("both")) opt.dir = Direction::Both;
            else if (m == QLatin1String("up")) opt.dir = Direction::Up;
            else if (m == QLatin1String("down")) opt.dir = Direction::Down;
            else if (m == QLatin1String("full")) opt.dir = Direction::Full;
            else { err << "error: --dir must be both|up|down|full\n"; err.flush(); return 2; }
            continue;
        }
        if (a == QLatin1String("--limit")) {
            if (i + 1 >= args.size()) { err << "error: --limit needs a value\n"; err.flush(); return 2; }
            bool ok; const quint64 lim = args.at(++i).toULongLong(&ok);
            if (!ok || lim < 1 || lim > 100000000) { err << "error: --limit must be 1..100000000\n"; err.flush(); return 2; }
            opt.limit = lim;
            continue;
        }
        if (a == QLatin1String("--gui")) continue;   // handled in main()
        if (a.startsWith(QLatin1Char('-'))) {
            bool hasDigit = false;
            for (int k = 0; k < a.size(); ++k)
                if (a.at(k).isDigit()) { hasDigit = true; break; }
            if (!hasDigit) { err << "error: unknown option '" << a << "' — try --help\n"; err.flush(); return 2; }
        }
        opt.positionals << a;
    }

    if (opt.selfTest) { const int c = runSelfTest(out); out.flush(); return c; }

    if (opt.positionals.size() != 1) {
        if (opt.positionals.isEmpty()) out << helpText();
        else err << "error: expected exactly one START number\n";
        out.flush(); err.flush();
        return 2;
    }
    quint64 start = 0;
    if (!parseNumber(opt.positionals.first(), &start)) {
        err << "error: '" << opt.positionals.first() << "' is not a valid number (max 18446744073709551615)\n";
        err.flush();
        return 2;
    }

    FinderParams p;
    p.start = start;
    p.batch = opt.batch;
    p.dir = opt.dir;
    p.limit = opt.limit;
    p.verbose = opt.verbose;

    const FinderReport r = findNearest(p);
    printFinderReport(out, r, p, opt.quiet);
    out.flush();
    err.flush();
    return (r.startIsPrime || r.foundUp || r.foundDown) ? 0 : 1;
}

/* =========================================================================
 *  GUI  (no Q_OBJECT on purpose: file needs no moc pass)
 * ========================================================================= */

class FinderWindow : public QWidget
{
public:
    explicit FinderWindow(const QString &prefill, QWidget *parent = nullptr)
        : QWidget(parent)
    {
        setWindowTitle(QStringLiteral("Prime Finder — batched bidirectional (Qt %1)").arg(QT_VERSION_STR));
        resize(680, 700);

        QFont mono(QStringLiteral("Monospace"));
        mono.setStyleHint(QFont::TypeWriter);

        QLabel *title = new QLabel(QStringLiteral("Prime Finder"), this);
        QFont tf = title->font();
        tf.setPointSize(tf.pointSize() + 6);
        tf.setBold(true);
        title->setFont(tf);

        QLabel *subtitle = new QLabel(
            QStringLiteral("Nearest prime search in alternating bands: N up, N down, N up, … "
                           "never runs far in one direction before checking the other"), this);
        subtitle->setWordWrap(true);
        subtitle->setStyleSheet(QStringLiteral("color:#666;"));

        m_start = new QLineEdit(this);
        m_start->setFont(mono);
        m_start->setPlaceholderText(QStringLiteral("start number <= 18,446,744,073,709,551,615"));
        if (!prefill.isEmpty()) m_start->setText(prefill);

        QPushButton *btnRandom = new QPushButton(QStringLiteral("Random"), this);
        QPushButton *btnFind   = new QPushButton(QStringLiteral("Find  ✓"), this);

        QLabel *batchLabel = new QLabel(QStringLiteral("Band size:"), this);
        m_batch = new QSpinBox(this);
        m_batch->setRange(1, 100000);
        m_batch->setValue(50);
        m_batch->setSuffix(QStringLiteral(" values/dir"));

        QLabel *dirLabel = new QLabel(QStringLiteral("Direction:"), this);
        m_dir = new QComboBox(this);
        m_dir->addItem(QStringLiteral("Alternating bands — nearest prime (recommended)"));
        m_dir->addItem(QStringLiteral("Up only — next prime"));
        m_dir->addItem(QStringLiteral("Down only — previous prime"));
        m_dir->addItem(QStringLiteral("Both fully — nearest up AND nearest down"));

        QLabel *limitLabel = new QLabel(QStringLiteral("Max distance:"), this);
        m_limit = new QSpinBox(this);
        m_limit->setRange(1, 10000000);
        m_limit->setValue(1000000);

        m_verdict = new QLabel(this);
        m_verdict->setAlignment(Qt::AlignCenter);
        m_verdict->setMinimumHeight(64);
        applyVerdict(QStringLiteral("Enter a start value and press Find."), 0);

        m_detail = new QLabel(this);
        m_detail->setFont(mono);
        m_detail->setTextFormat(Qt::PlainText);
        m_detail->setTextInteractionFlags(Qt::TextSelectableByMouse);
        m_detail->setWordWrap(true);
        m_detail->setMinimumHeight(150);
        m_detail->setAlignment(Qt::AlignTop | Qt::AlignLeft);
        m_detail->setStyleSheet(QStringLiteral(
            "background:#f7f6f3; border:1px solid #ddd; border-radius:6px; padding:10px;"));

        m_trace = new QListWidget(this);
        m_trace->setFont(mono);
        QGroupBox *traceBox = new QGroupBox(QStringLiteral("Band trace"), this);
        QVBoxLayout *tLay = new QVBoxLayout(traceBox);
        tLay->addWidget(m_trace);

        QHBoxLayout *startRow = new QHBoxLayout();
        startRow->addWidget(m_start, 1);
        startRow->addWidget(btnRandom);
        startRow->addWidget(btnFind);

        QHBoxLayout *optRow = new QHBoxLayout();
        optRow->addWidget(batchLabel);
        optRow->addWidget(m_batch);
        optRow->addWidget(dirLabel);
        optRow->addWidget(m_dir, 1);
        optRow->addWidget(limitLabel);
        optRow->addWidget(m_limit);

        QVBoxLayout *lay = new QVBoxLayout(this);
        lay->addWidget(title);
        lay->addWidget(subtitle);
        lay->addSpacing(6);
        lay->addLayout(startRow);
        lay->addLayout(optRow);
        lay->addWidget(m_verdict);
        lay->addWidget(m_detail);
        lay->addWidget(traceBox, 1);

        connect(btnFind, &QPushButton::clicked, this, [this] { runFind(); });
        connect(m_start, &QLineEdit::returnPressed, this, [this] { runFind(); });
        connect(btnRandom, &QPushButton::clicked, this, [this] {
            quint64 v = QRandomGenerator::global()->generate64() >> 2; // 62-bit
            if (v < 4) v = 4;
            m_start->setText(QString::number(v));
            runFind();
        });

        m_start->setFocus();
    }

    void runFind()
    {
        quint64 start = 0;
        if (!parseNumber(m_start->text(), &start)) {
            applyVerdict(QStringLiteral("Invalid input"), 3);
            m_detail->setText(QStringLiteral(
                "Could not parse the input.\n"
                "Allowed: up to 20 digits, maximum 18,446,744,073,709,551,615.\n"
                "Separators , _ ' and spaces are ignored."));
            m_trace->clear();
            return;
        }

        FinderParams p;
        p.start = start;
        p.batch = m_batch->value();
        p.dir = static_cast<Direction>(m_dir->currentIndex());
        p.limit = (quint64)m_limit->value();
        p.verbose = false;

        const FinderReport r = findNearest(p);
        const bool found = r.foundUp || r.foundDown;

        if (r.startIsPrime) {
            applyVerdict(QString("%1 IS PRIME").arg(grouped(r.start)), 1);
        } else if (!found) {
            applyVerdict(QStringLiteral("NO PRIME FOUND"), 3);
        } else if (r.equidistant) {
            applyVerdict(QString("%1  ⇄  %2   (±%3)")
                         .arg(grouped(r.downPrime)).arg(grouped(r.upPrime)).arg(r.upDist), 1);
        } else if (r.foundUp && (!r.foundDown || r.upDist <= r.downDist)) {
            applyVerdict(QString("%1   ( +%2 ↑ )").arg(grouped(r.upPrime)).arg(r.upDist), 1);
        } else {
            applyVerdict(QString("%1   ( −%2 ↓ )").arg(grouped(r.downPrime)).arg(r.downDist), 1);
        }

        m_detail->setText(finderDetailText(r, p));

        m_trace->clear();
        for (const QString &line : r.trace)
            m_trace->addItem(line);
    }

private:
    void applyVerdict(const QString &text, int kind)
    {
        static const char *colors[][2] = {
            { "#555555", "#eeeeee" },
            { "#157f3d", "#e8f5e9" },
            { "#c0392b", "#fdecea" },
            { "#b07d00", "#fff8e1" },
        };
        m_verdict->setText(text);
        m_verdict->setStyleSheet(QStringLiteral(
            "font-size:22px; font-weight:bold; color:%1; background:%2;"
            "border:1px solid %1; border-radius:6px; padding:12px;")
            .arg(QLatin1String(colors[kind][0]), QLatin1String(colors[kind][1])));
    }

    QLineEdit   *m_start = nullptr;
    QSpinBox    *m_batch = nullptr;
    QComboBox   *m_dir = nullptr;
    QSpinBox    *m_limit = nullptr;
    QLabel      *m_verdict = nullptr;
    QLabel      *m_detail = nullptr;
    QListWidget *m_trace = nullptr;
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
        QApplication app(argc, argv);
        app.setApplicationName(QStringLiteral("primefinder"));
        app.setApplicationVersion(QStringLiteral("1.0"));
        QString prefill;
        for (int i = 0; i < args.size(); ++i) {
            if (args.at(i) != QLatin1String("--gui") && !args.at(i).startsWith(QLatin1Char('-'))) {
                prefill = args.at(i);
                break;
            }
        }
        FinderWindow w(prefill);
        w.show();
        if (!prefill.isEmpty())
            w.runFind();
        return app.exec();
    }

    QCoreApplication app(argc, argv);
    app.setApplicationName(QStringLiteral("primefinder"));
    app.setApplicationVersion(QStringLiteral("1.0"));
    return runCli(args);
}
