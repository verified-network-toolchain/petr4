from collections import defaultdict
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

    def packet_in(self,switch,in_port,packet):
        print(f"Petr4: packet_in({switch}, {in_port}, {packet})")

    def counter_response(self,switch, name, index, count):
        print(f"Petr4: counter_response({switch}, {name}, {index}, {count})")

    def counter_request(self,switch,name, index):
        print(f"Petr4: counter_request({switch}, {name}, {index})")
        msg = json.dumps(["CounterRequest", { "name" : name, "index" : index }])
        self.msg_queues[switch].put(msg)
        return
        
    def insert(self,switch,entry):
        print(f"Petr4: insert({switch}, {entry})")
        msg = json.dumps(["Insert", entry.to_json()])
        self.msg_queues[switch].put(msg)
        return

    def packet_out(self,switch,in_port,packet):
        print(f"Petr4: packet_out({switch}, {in_port}, {packet})")
        msg = json.dumps(["PacketOut",
                          { "switch" : switch,
                            "in_port" : in_port,
                            "packet" : packet }])
        self.msg_queues[switch].put(msg)
        return

    class Hello(RequestHandler):
        def initialize(self, app):
            self.app = app
        def post(self):
            hello = tornado.escape.json_decode(self.request.body)[1]
            self.app.switch_up(hello["switch"], hello["ports"])
            self.write("Hello")

    class Event(RequestHandler):
        def initialize(self, app):
            self.app = app
        async def post(self):
            event = tornado.escape.json_decode(self.request.body)[1]
            switch = event["switch"]
            msg = await self.app.msg_queues[switch].get()
            self.write(msg)

    class PacketIn(RequestHandler):
        def initialize(self, app):
            self.app = app
        async def post(self):
            packet_in = tornado.escape.json_decode(self.request.body)[1]
            switch = packet_in["switch"]
            in_port = packet_in["in_port"]
            packet = packet_in["packet"]            
            self.app.packet_in(switch,in_port,packet)

    class CounterResponse(RequestHandler):
        def initialize(self, app):
            self.app = app
        async def post(self):
            counter_response = tornado.escape.json_decode(self.request.body)[1]
            switch = counter_response["switch"]
            name = counter_response["name"]
            index = counter_response["index"]            
            count = counter_response["count"]            
            self.app.counter_response(switch,name,index,count)
            
    def __init__(self, port=9000):
        self.port = port
        self.msg_queues = defaultdict(lambda:Queue())
        application = Application([
            ('/hello', self.Hello, { "app" : self } ),
            ('/event', self.Event, { "app" : self } ),
            ('/packet_in', self.PacketIn, { "app" : self }),
            ('/counter_response', self.CounterResponse, { "app" : self })])
        self.http_server = HTTPServer(application)

    def start(self):
        print(f"Petr4: starting controller on {self.port}.")
        self.http_server.listen(self.port)
        IOLoop.instance().start()


 
