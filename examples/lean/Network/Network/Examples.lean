import Network.Protocol
import Network.Types
import Network.Checks
namespace Network

/-- Example networks. -/
def net1 : Network := { name := "net1", public := false }
def net2 : Network := { name := "net2", public := false }
def net3 : Network := { name := "net3", public := true }
def net4 : Network := { name := "net4", public := true }

/-- Example ports. -/
def p1 : Port := { name := "p1", network := net1 }
def p2 : Port := { name := "p2", network := net3 }
def p3 : Port := { name := "p3", network := net2 }

/-- Example servers. -/
def app     : Server := { name := "app",     protocols := [.https, .ssh], ports := [p1, p2, p3] }
def db      : Server := { name := "db",      protocols := [.mysql],        ports := [p3] }
def cache   : Server := { name := "cache",   protocols := [.memcache],     ports := [p3] }
def ci      : Server := { name := "ci",      protocols := [.http],         ports := [p1, p2] }
def busybox : Server := { name := "busybox", protocols := [.telnet],      ports := [p1] }

/-- Collections for evaluation. -/
def servers : List Server := [app, db, cache, ci, busybox]
def networks : List Network := [net1, net2, net3, net4]
def ports : List Port := [p1, p2, p3]

#eval goodServerList servers   -- returns all "good" servers
#eval badServerList servers    -- returns the rest

end Network
