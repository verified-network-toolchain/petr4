import uuid, sys, json, base64, time, array, binascii
from datetime import timedelta
from functools import partial
from tornado import httpclient
from tornado.httpclient import AsyncHTTPClient, HTTPRequest
from tornado.ioloop import IOLoop
from tornado import gen

class App(object):

    """This method can be overridden by the application. By default, it simply
       prints the event."""
    def switch_up(self,switch_id,ports):
        print(f"switch_up(switch_id={switch_id})")

    """This method can be overridden by the application. By default, it simply
       prints the event."""
    def switch_down(self,switch_id):
        print (f"switch_down(switch_id={switch_id})")

    def connected(self):
        print("established connection to Petr4 controller")

    def insert(self, entry):
        entry_json = json.dumps(entry.to_json())
        url = "http://%s:%s/%s/insert" % (self.petr4_http_host, self.petr4_http_port, self.client_id)
        request = HTTPRequest(url,method='POST',body=entry_json)
        return self.__http_client.fetch(request)

    def __init__(self):
        if not hasattr(self, 'client_id'):
            self.client_id = uuid.uuid4().hex
            print(f"No client_id specified. Using {self.client_id}")
        if not hasattr(self, 'petr4_http_host'):
            self.petr4_http_host = "localhost"
        if not hasattr(self, 'petr4_http_port'):
            self.petr4_http_port = "9000"
        self.__http_client = AsyncHTTPClient()
        self.__connect()

    def __connect(self):
        url = "http://%s:%s/version" % (self.petr4_http_host, self.petr4_http_port)
        req = HTTPRequest(url, method='GET',request_timeout=0)
        resp_fut = self.__http_client.fetch(req)
        IOLoop.instance().add_future(resp_fut, self.__handle_connect)

    def __handle_connect(self, response_future):

        try:
            response = response_future.result()
            self.__poll_event()
            self.connected()
        except httpclient.HTTPError as e:
            if e.code == 599:
                print("Petr4 not running, re-trying....")
                one_second = timedelta(seconds = 1)
                IOLoop.instance().add_timeout(one_second, self.__connect)
            else:
                raise e

    def start_event_loop(self):
        print("Starting the tornado event loop (does not return).")
        IOLoop.instance().start()

    def __poll_event(self):
        url = "http://%s:%s/%s/event" % (self.petr4_http_host, self.petr4_http_port, self.client_id)
        req = HTTPRequest(url, method='GET',request_timeout=0)
        resp_fut = self.__http_client.fetch(req)
        IOLoop.instance().add_future(resp_fut, self.__handle_event)

    def __handle_event(self, response):
        try: 
            event =  json.loads(response.result().body)
            if isinstance(event, list) or 'type' not in event:
                typ = "UNKNOWN"
            else:
                typ = event['type']
            if typ == 'switch_up':
                switch_id = event['switch_id']
                ports = event['ports']
                self.switch_up(switch_id, ports)
            elif typ == 'switch_down':
                switch_id = event['switch_id']
                self.switch_down(switch_id)

            self.__poll_event()

        except httpclient.HTTPError as e:
            if e.code == 599:
                current_time = time.strftime("%c")
                print(f"{current_time} Petr4 crashed, re-trying in 5 seconds....")
                five_seconds = timedelta(seconds = 5)

                # We wait for a connect instead of going through the loop again.
                IOLoop.instance().add_timeout(five_seconds,self.__connect)
            else:
                raise e

 
