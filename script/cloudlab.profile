"""16 r650 instances for running SMART"""

#
# NOTE: This code was machine converted. An actual human would not
#       write code like this!
#

# Import the Portal object.
import geni.portal as portal
# Import the ProtoGENI library.
import geni.rspec.pg as pg
# Import the Emulab specific extensions.
import geni.rspec.emulab as emulab

# Create a portal object,
pc = portal.Context()

# Create a Request object to start building the RSpec.
request = pc.makeRequestRSpec()

# Node node-0
node_0 = request.RawPC('node-0')
node_0.routable_control_ip = True
node_0.hardware_type = 'r650'
node_0.installRootKeys(True, True)
node_0.disk_image = 'urn:publicid:IDN+emulab.net+image+emulab-ops//UBUNTU18-64-STD'
iface0 = node_0.addInterface('interface-1')

# Node node-1
node_1 = request.RawPC('node-1')
node_1.routable_control_ip = True
node_1.hardware_type = 'r650'
node_1.installRootKeys(True, True)
node_1.disk_image = 'urn:publicid:IDN+emulab.net+image+emulab-ops//UBUNTU18-64-STD'
iface1 = node_1.addInterface('interface-0')

# Node node-2
node_2 = request.RawPC('node-2')
node_2.routable_control_ip = True
node_2.hardware_type = 'r650'
node_2.installRootKeys(True, True)
node_2.disk_image = 'urn:publicid:IDN+emulab.net+image+emulab-ops//UBUNTU18-64-STD'
iface2 = node_2.addInterface('interface-2')

# Node node-3
node_3 = request.RawPC('node-3')
node_3.routable_control_ip = True
node_3.hardware_type = 'r650'
node_3.installRootKeys(True, True)
node_3.disk_image = 'urn:publicid:IDN+emulab.net+image+emulab-ops//UBUNTU18-64-STD'
iface3 = node_3.addInterface('interface-3')

# Node node-4
node_4 = request.RawPC('node-4')
node_4.routable_control_ip = True
node_4.hardware_type = 'r650'
node_4.installRootKeys(True, True)
node_4.disk_image = 'urn:publicid:IDN+emulab.net+image+emulab-ops//UBUNTU18-64-STD'
iface4 = node_4.addInterface('interface-4')


# Link link-0
link_0 = request.Link('link-0')
link_0.Site('undefined')
link_0.addInterface(iface1)
link_0.addInterface(iface0)
link_0.addInterface(iface2)
link_0.addInterface(iface3)
link_0.addInterface(iface4)



# Print the generated rspec
pc.printRequestRSpec(request)
