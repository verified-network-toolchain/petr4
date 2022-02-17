from http.server import BaseHTTPRequestHandler, HTTPServer
import time

reqs = 0
thresh = 10
sleep_time = 0.1

class handler(BaseHTTPRequestHandler):
    def do_GET(self):
        global reqs

        self.send_response(200)
        self.send_header('Content-type','text/html')
        self.end_headers()

        message = "Hello, World!"
        reqs += 1
        if reqs == thresh:
            time.sleep(sleep_time)
            reqs = 0
        
        self.wfile.write(bytes(message, "utf8"))
        print("served")

with HTTPServer(('0.0.0.0', 8000), handler) as server:
    server.serve_forever()
