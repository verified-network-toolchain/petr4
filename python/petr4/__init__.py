import uuid, sys, json, base64, time, array, binascii
import asyncio
import tornado
from tornado import httpserver
from tornado.web import RequestHandler
from tornado.httpserver import HTTPServer
from tornado.web import Application
from tornado.ioloop import IOLoop
from tornado.queues import Queue

class App(object):

    def switch_up(self,switch,ports):
        print(f"Petr4: switch_up({switch}, {ports})")

    def insert(self, switch, entry):
        print(f"Petr4: insert({switch}, {entry})")
        msg = json.dumps(["Insert", entry.to_json()])
        self.msg_queue.put(msg)
        return

    class Hello(RequestHandler):
        def initialize(self, app):
            self.app = app
        def post(self):
            hello = tornado.escape.json_decode(self.request.body)[1]
            self.app.switch_up(hello["switch"], hello["ports"])
            self.write("Ok")

    class Event(RequestHandler):
        def initialize(self, app):
            self.app = app
        async def get(self):
            msg = await self.app.msg_queue.get()
            self.write(msg)

    def __init__(self, port=9000):
        self.port = port
        self.msg_queue = Queue()
        application = Application([
            ('/hello', self.Hello, { "app" : self } ),
            ('/event', self.Event, { "app" : self } )])
        self.http_server = HTTPServer(application)

    def start(self):
        print(f"Petr4: starting controller on {self.port}.")
        self.http_server.listen(self.port)
        IOLoop.instance().start()


 
