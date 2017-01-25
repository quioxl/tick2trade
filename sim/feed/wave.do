onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb/reset_n
add wave -noupdate /tb/clk
add wave -noupdate -group {Avalon Master} /tb/avl_master_if/data
add wave -noupdate -group {Avalon Master} /tb/avl_master_if/empty
add wave -noupdate -group {Avalon Master} /tb/avl_master_if/endofpacket
add wave -noupdate -group {Avalon Master} /tb/avl_master_if/error
add wave -noupdate -group {Avalon Master} /tb/avl_master_if/ready
add wave -noupdate -group {Avalon Master} /tb/avl_master_if/startofpacket
add wave -noupdate -group {Avalon Master} /tb/avl_master_if/valid
add wave -noupdate -group {Avalon Slave} /tb/avl_slave_if/data
add wave -noupdate -group {Avalon Slave} /tb/avl_slave_if/empty
add wave -noupdate -group {Avalon Slave} /tb/avl_slave_if/endofpacket
add wave -noupdate -group {Avalon Slave} /tb/avl_slave_if/error
add wave -noupdate -group {Avalon Slave} /tb/avl_slave_if/ready
add wave -noupdate -group {Avalon Slave} /tb/avl_slave_if/startofpacket
add wave -noupdate -group {Avalon Slave} /tb/avl_slave_if/valid
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {193 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 500
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits fs
update
WaveRestoreZoom {0 ns} {4667 ns}