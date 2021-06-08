from petr4 import App
from topo import *
from petr4.runtime import *
from tornado.ioloop import *
from struct import pack
import binascii

class LearningApp(App):

    def switch_up(self,switch,ports):
        print(f"{switch} is up!")
        super().switch_up(switch, ports)
                
    def packet_in(self,switch,in_port,packet):
        # TODO
        super().packet_in(switch, in_port, packet)
        
    def __init__(self, port=9000):
        super().__init__(port)

app = LearningApp()
app.start()
