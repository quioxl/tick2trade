onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/clk
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/reset_n
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/ready
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/valid
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/startofpacket
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/endofpacket
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/data
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/empty
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/error
add wave -noupdate -expand -group {Host Interface} /tb/host_if/clk
add wave -noupdate -expand -group {Host Interface} /tb/host_if/reset_n
add wave -noupdate -expand -group {Host Interface} /tb/host_if/in_config_valid
add wave -noupdate -expand -group {Host Interface} /tb/host_if/in_config_data
add wave -noupdate -expand -group {Host Interface} /tb/host_if/in_config_accept
add wave -noupdate -expand -group {Order Interface} /tb/order_if/clk
add wave -noupdate -expand -group {Order Interface} /tb/order_if/reset_n
add wave -noupdate -expand -group {Order Interface} /tb/order_if/data
add wave -noupdate -expand -group {Order Interface} /tb/order_if/ready
add wave -noupdate -expand -group {Order Interface} /tb/order_if/valid
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {11535233 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 2
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ps} {232096 ps}
