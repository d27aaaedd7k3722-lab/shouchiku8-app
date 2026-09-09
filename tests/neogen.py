import sys, os, sqlite3, tempfile, json
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import app

TPL = open('/home/user/shouchiku8-app/template_toyota.neo','rb').read()

def gen(items, cust=None, ins=None, sp=0, expenses=None, incl=False, beta=True):
    return app.generate_neo_file(TPL, cust or {}, items, sp, ins or {}, expenses or {}, incl, beta)

def unpack(neo_bytes):
    real_ck = app.find_real_cks(neo_bytes)
    full_raw = app.decompress_neo(neo_bytes, real_ck)
    mgmt, entries = app.parse_entries(neo_bytes, real_ck[0])
    return app.extract_files(full_raw, entries)

def opendb(blob):
    tf = tempfile.NamedTemporaryFile(suffix='.db', delete=False)
    tf.write(blob); tf.close()
    return sqlite3.connect(tf.name)

def rows(conn, sql):
    cur = conn.cursor(); cur.execute(sql)
    cols = [d[0] for d in cur.description]
    return cols, cur.fetchall()
