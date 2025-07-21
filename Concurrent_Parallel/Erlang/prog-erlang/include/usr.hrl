% usr记录定义
-record(usr, {
  msisdn,      % int(), 作为主键, 例: 71234567
  id,          % term()
  status = enabled,    % atom(), enabled | disabled
  plan,        % atom(), prepay | postpay
  services = []    % [atom()], service flag list
}).